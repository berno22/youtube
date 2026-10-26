/* Tesla-engine.js - Drive-proof live TV playback for the livetv page.
 *
 * WHY THIS EXISTS
 * ---------------
 * The normal player on this page is video.js + application/x-mpegURL, which
 * means MSE feeding a <video> element. When the car is in Drive, that is the
 * thing that freezes: the picture locks while the audio keeps going. MSE and the
 * media element are the problem, not the stream.
 *
 * So this player never creates a media element for the video path. It fetches
 * the MPEG-TS segments itself and decodes them with WebCodecs, painting each
 * decoded frame onto a <canvas>:
 *
 *   .ts -> mux.js mp4.Transmuxer -> fMP4 -> mp4box.js -> elementary samples
 *       -> WebCodecs VideoDecoder -> canvas
 *       -> WebCodecs AudioDecoder -> ring buffer in an AudioWorklet -> speakers
 *
 * That is the same pipeline proven on the Sky Sports F1 page, generalised for
 * many channels and made restartable.
 *
 * WHAT IS DIFFERENT FROM THE F1 PAGE, AND WHY
 * -------------------------------------------
 * 1. open()/close() instead of a one-shot start(). A channel grid switches
 *    streams constantly, so every decoder, timer and audio node has to be
 *    torn down or they pile up: each switch would leak a VideoDecoder and a
 *    second audio graph, and the page would get slower the more you flick
 *    through channels.
 * 2. Master playlists are followed (#EXT-X-STREAM-INF). F1TV serves a master
 *    playlist whose variant is chosen by bandwidth, and the master has no
 *    segments of its own - reading it as a media playlist yields nothing.
 * 3. Non-media tracks are ignored. F1TV's TS carries scte_35 and timed_id3
 *    alongside the real audio; taking "the first audio track" would decode
 *    SCTE-35 ad markers as if they were sound.
 * 4. Queue caps scale with the real frame rate. Channels run at 25, 30 and
 *    59.94fps, and a cap sized for 25fps overflows on a 60fps one, dropping
 *    exactly the frames that were about to be shown.
 * 5. The audio sample rate comes from the stream, not a hardcoded 48000.
 *    nasa.4k.us is 32kHz; everything else is 48kHz. Forcing 48kHz on a 32kHz
 *    track makes the decoder resample or fail, and the ring then runs at the
 *    wrong rate against the device clock.
 * 6. Canvas size is capped. Decoding happens at source resolution, but the
 *    canvas is scaled down: a 1080p canvas at 60fps is pure paint cost for no
 *    visible gain in a car.
 */
(function (global) {
  'use strict';

  // How much already-downloaded media to keep ahead of playback. This is the
  // cushion that absorbs a slow segment fetch or a decode hiccup without the
  // listener hearing a gap. VOD starts at a minute and grows one second of
  // extra buffer for every second played, up to three minutes. Live keeps a
  // smaller cushion so it does not fall too far behind the edge.
  var VOD_BUFFER_START_S = 60;
  var VOD_BUFFER_MAX_S = 180;
  // Start live playback behind the edge so the segments ahead of us already
  // exist. That is what makes a real live cushion possible; joining at the
  // newest segment leaves nothing available to download until it airs.
  var LIVE_EDGE_DELAY_S = 35;
  var LIVE_BUFFER_TARGET_S = 30;
  // One more segment can arrive after the target is checked, so the sample
  // queues need room for that overshoot as well.
  var BUFFER_OVERSHOOT_S = 20;
  var MAX_VIDEO_BUFFER_SAMPLES =
    Math.ceil((VOD_BUFFER_MAX_S + BUFFER_OVERSHOOT_S) * 60) + 16;
  var MAX_AUDIO_BUFFER_FRAMES =
    Math.ceil((VOD_BUFFER_MAX_S + BUFFER_OVERSHOOT_S) * 48000 / 1024) + 16;

  function bufferTargetFor(s) {
    if (s.live) return LIVE_BUFFER_TARGET_S;
    var elapsed = s.vT0 >= 0 ? Math.max(0, (Date.now() - s.vT0) / 1000) : 0;
    if (elapsed > (s.maxPlayed || 0)) s.maxPlayed = elapsed;
    return Math.min(VOD_BUFFER_MAX_S, VOD_BUFFER_START_S + Math.floor(s.maxPlayed || 0));
  }

  function liveStartIndex(segs) {
    var total = 0;
    for (var i = segs.length - 1; i >= 0; i--) {
      total += Number(segs[i].dur) || 0;
      if (total >= LIVE_EDGE_DELAY_S) return i;
    }
    return 0;
  }

  // How far ahead of its due time audio is decoded and poured into the ring.
  // A ring holding exactly this much is playing the same media instant the
  // picture is showing - the decode lead and the buffered depth cancel each
  // other - so this is both the feed horizon and the target the sync trim
  // steers to. It and AUDIO_LEAD_S must stay in step.
  var AUDIO_LEAD_MS = 1500;
  var AUDIO_LEAD_S = AUDIO_LEAD_MS / 1000;

  var has = function (k) { return typeof global[k] !== 'undefined'; };

  function missingLibs(needAudio) {
    var miss = [];
    if (!has('muxjs') || !global.muxjs.mp4 || !global.muxjs.mp4.Transmuxer) miss.push('mux.js');
    if (!has('MP4Box')) miss.push('mp4box.js');
    if (!has('VideoDecoder') || !has('EncodedVideoChunk')) miss.push('WebCodecs VideoDecoder');
    if (needAudio && (!has('AudioDecoder') || !has('AudioData'))) miss.push('WebCodecs AudioDecoder');
    return miss;
  }

  // ==========================================================================
  // The ring buffer, as an AudioWorklet.
  //
  // The obvious implementation - one AudioBuffer plus a BufferSourceNode per
  // decoded audio frame - sounds bad. At 1024 samples a frame that is ~47
  // buffer sources per second, each scheduled independently, and any sub-block
  // scheduling error becomes a discontinuity: a click on every boundary. It
  // also allocates a buffer per frame.
  //
  // Instead the decoder output is poured into a ring buffer that the worklet
  // pulls at exactly one steady rate. One uninterrupted stream, no per-block
  // seams, and the decoder can run ahead into the buffer while playback stays
  // smooth.
  // ==========================================================================
  var RING_WORKLET = [
    'class LoFiRing extends AudioWorkletProcessor {',
    '  constructor(opts) {',
    '    super();',
    '    const p = (opts && opts.processorOptions) || {};',
    '    this.cap = p.capacity || sampleRate * 8;',
    '    this.ch = [new Float32Array(this.cap), new Float32Array(this.cap)];',
    '    this.w = 0; this.r = 0; this.avail = 0; this.pos = 0;',
    '    this.underruns = 0; this.fed = false; this.tick = 0;',
    // The stream's rate is not always the device's. nasa.4k.us is 32kHz and
    // the AudioContext is 48kHz, so reading one source sample per output sample
    // drains the ring 1.5x too fast and it starves continuously - a permanent
    // crackle. Linear interpolation between the source rate and the device rate
    // keeps the two clocks in step.
    '    this.srcRate = p.sourceRate || sampleRate;',
    '    this.step = this.srcRate / sampleRate;',
    // A trim of 1 reads at the stream's own rate. The main thread nudges it a
    // fraction of a percent either way to hold the ring at the depth that
    // keeps the sound level with the picture; see trimAudio().
    '    this.trim = 1;',
    '    this.port.onmessage = (e) => {',
    '      const d = e.data;',
    // Switching channels must not play out the tail of the previous one, so the
    // ring is emptied on a switch. fed resets too, so the underrun counter
    // measures the new channel rather than inheriting the old one's.
    '      if (d && d.flush) { this.w = 0; this.r = 0; this.avail = 0; this.pos = 0; this.fed = false; return; }',
    '      if (d && d.trim) { this.trim = d.trim; return; }',
    // A new channel may arrive at a different rate. Re-step and empty, because
    // the existing contents are in the old rate's timeline.
    '      if (d && d.rate) {',
    '        this.srcRate = d.rate; this.step = d.rate / sampleRate;',
    '        this.w = 0; this.r = 0; this.avail = 0; this.pos = 0; this.fed = false;',
    '        return;',
    '      }',
    '      const frames = d;',
    '      if (!frames || !frames.length) return;',
    '      const n = frames[0].length;',
    '      if (this.avail + n > this.cap) {',
    '        const room = Math.max(0, this.cap - this.avail);',
    '        for (let i = 0; i < room; i++) {',
    '          this.ch[0][this.w] = frames[0][i]; this.ch[1][this.w] = frames[1][i];',
    '          this.w = (this.w + 1) % this.cap;',
    '        }',
    '        this.avail += room;',
    '        return;',
    '      }',
    '      for (let i = 0; i < n; i++) {',
    '        this.ch[0][this.w] = frames[0][i]; this.ch[1][this.w] = frames[1][i];',
    '        this.w = (this.w + 1) % this.cap;',
    '      }',
    '      this.avail += n; this.fed = true;',
    '    };',
    '  }',
    '  process(inputs, outputs) {',
    '    const out = outputs[0];',
    '    if (!out || !out.length) return true;',
    '    const n = out[0].length;',
    '    let starved = false;',
    '    const L = this.ch[0], R = this.ch[1];',
    // One read per OUTPUT SAMPLE POSITION, not per channel. Advancing the read
    // pointer inside the per-channel loop consumed 2 samples per output frame on
    // a stereo stream, so the ring drained at exactly double rate, always ran
    // dry, and gave the right channel the wrong samples.
    '    const st = this.step * this.trim;',
    '    for (let i = 0; i < n; i++) {',
    '      let l = 0, r = 0;',
    '      if (this.avail >= 1) {',
    '        const i0 = this.pos | 0;',
    '        const i1 = i0 + 1;',
    '        const f = this.pos - i0;',
    '        const a0 = i0 % this.cap, a1 = i1 % this.cap;',
    '        if (f > 0) {',
    '          l = L[a0] + (L[a1] - L[a0]) * f;',
    '          r = R[a0] + (R[a1] - R[a0]) * f;',
    '        } else { l = L[a0]; r = R[a0]; }',
    '        this.pos += st;',
    '        this.avail -= st;',
    '      } else { starved = true; }',
    '      out[0][i] = l;',
    '      if (out.length > 1) out[1][i] = r;',
    '      if (out.length > 2) for (let c = 2; c < out.length; c++) out[c][i] = l;',
    '      this.sum = (this.sum || 0) + l * l;',
    '      this.count = (this.count || 0) + 1;',
    '      if (this.count >= 2048) { this.rms = Math.sqrt(this.sum / this.count); this.count = 0; this.sum = 0; }',
    '    }',
    // Report sparingly. process() runs every 128 samples, ~375 times a second,
    // and posting on every call floods the main thread, which starves the paint
    // timer and the decoder feed. A tick every ~10 quanta is plenty.
    '    this.tick++;',
    // Only count a dropout once audio has actually been supplied. The graph is
    // built at tap time, well before the first segment is demuxed, so the ring
    // is legitimately empty for the first seconds - that is silence because
    // there is nothing yet, not a gap in playback.
    '    if (starved && this.fed) {',
    '      this.underruns++;',
    '      if (this.tick > 8) { this.tick = 0; this.port.postMessage({ starved: 1, underruns: this.underruns }); }',
    '    } else if (this.tick >= 8) {',
    '      this.tick = 0;',
    '      this.port.postMessage({ depth: this.avail / this.srcRate, rms: this.rms || 0 });',
    '    }',
    '    return true;',
    '  }',
    '}',
    "registerProcessor('lofi-ring', LoFiRing);"
  ].join('\n');

  function hex2(n) { return (n == null ? 0 : n).toString(16).padStart(2, '0'); }

  // avcC record -> the flat AVCDecoderConfigurationRecord WebCodecs wants.
  function avcCDescription(avcC) {
    if (!avcC || !avcC.SPS || !avcC.SPS.length || !avcC.PPS || !avcC.PPS.length) return undefined;
    var parts = [avcC.configurationVersion, avcC.AVCProfileIndication,
      avcC.profile_compatibility, avcC.AVCLevelIndication,
      0xFC | (avcC.lengthSizeMinusOne & 3), 0xE0 | avcC.SPS.length];
    for (var i = 0; i < avcC.SPS.length; i++) {
      var s = avcC.SPS[i].nalu;
      parts.push((s.length >> 8) & 255, s.length & 255);
      for (var j = 0; j < s.length; j++) parts.push(s[j]);
    }
    parts.push(avcC.PPS.length);
    for (var k = 0; k < avcC.PPS.length; k++) {
      var p = avcC.PPS[k].nalu;
      parts.push((p.length >> 8) & 255, p.length & 255);
      for (var m = 0; m < p.length; m++) parts.push(p[m]);
    }
    return new Uint8Array(parts);
  }

  // esds -> the AudioSpecificConfig WebCodecs wants for AAC.
  function ascFromEsds(esds) {
    try {
      var d = esds.esd.esdDescs[0].descs[0].descs;
      var i = 0;
      while (i < d.length) {
        if (d[i].tag === 0x05) return new Uint8Array(d[i].data);
        i++;
      }
    } catch (e) { /* fall through: the codec string alone is enough for most AAC */ }
    return undefined;
  }

  // ========================================================================
  // The player
  // ========================================================================
  function TeslaPlayer(opts) {
    this.opts = opts || {};
    this.canvas = this.opts.canvas;
    this.gl = null;
    this.ctx2d = this.canvas.getContext('2d', { alpha: false });
    // Cap the canvas. Decoding is at source resolution either way, but a 1080p
    // canvas repainted at 60fps is a lot of paint for a car display.
    this.maxW = this.opts.maxWidth || 1280;
    this.gainValue = this.opts.gain || 4;
    // Remembered rather than applied here. The gain node does not exist until
    // the audio graph is built on the first gesture, and a channel opened while
    // muted must not start audible just because finish() ran later.
    this.muted = !!this.opts.muted;
    this.gen = 0;          // bumped by close(); every async callback checks it
    this.live = null;      // the running stream, or null
    this.actx = null;      // AudioContext, kept across channels
    this.activated = false; // has a user gesture happened yet
    // The audio output chain, built once and shared by every channel.
    this.audio = { ready: false, pending: null, node: null, push: null, flush: null,
                   setRate: null, setTrim: null, rate: 0, sourceRate: 0, trim: 1,
                   path: '', modErr: '', depth: 0, rms: 0, underruns: 0,
                   gain: null, limiter: null, analyser: null, buf: null };
    this.listeners = {};
  }

  TeslaPlayer.prototype.on = function (ev, fn) {
    (this.listeners[ev] = this.listeners[ev] || []).push(fn);
    return this;
  };
  TeslaPlayer.prototype.emit = function (ev, data) {
    var l = this.listeners[ev];
    if (!l) return;
    for (var i = 0; i < l.length; i++) { try { l[i](data); } catch (e) {} }
  };

  // ---- audio unlock -------------------------------------------------------
  // Must happen inside a real user gesture. Creating the AudioContext later,
  // when the first segment finishes demuxing, is a network callback and not a
  // gesture: strict autoplay policies then leave the context suspended, every
  // sample is discarded, and you get a perfect picture with total silence and
  // no error anywhere.
  TeslaPlayer.prototype.unlock = function () {
    var self = this;
    var AC = global.AudioContext || global.webkitAudioContext;
    if (!AC) return Promise.resolve(false);
    this.activated = true;
    if (!this.actx) {
      try { this.actx = new AC(); } catch (e) { return Promise.resolve(false); }
    }
    var p = this.actx.state === 'suspended' ? this.actx.resume() : Promise.resolve();
    return p.then(function () {
      // Some engines only fully unlock on a real source.
      try {
        var b = self.actx.createBuffer(1, 1, 44100);
        var s = self.actx.createBufferSource();
        s.buffer = b; s.connect(self.actx.destination); s.start(0);
      } catch (e) {}
      // Build the ring while the gesture is still valid.
      return self.ensureAudio();
    }).catch(function () { return false; });
  };

  // A 1kHz tone through the same output chain. If this is silent, audio is not
  // reaching the speakers and the problem is the environment, not the decode
  // path - otherwise the two are indistinguishable.
  TeslaPlayer.prototype.tone = function () {
    if (!this.actx) { this.emit('note', 'no audio context'); return; }
    if (this.actx.state === 'suspended') this.actx.resume().catch(function () {});
    var t = this.actx.currentTime;
    var o = this.actx.createOscillator();
    var g = this.actx.createGain();
    o.frequency.value = 1000;
    g.gain.setValueAtTime(0.0001, t);
    g.gain.exponentialRampToValueAtTime(0.25, t + 0.02);
    g.gain.setValueAtTime(0.25, t + 0.4);
    g.gain.exponentialRampToValueAtTime(0.0001, t + 0.5);
    o.connect(g); g.connect(this.actx.destination);
    o.start(t); o.stop(t + 0.55);
    this.emit('note', 'tone played');
  };

  // ---- lifecycle ----------------------------------------------------------
  TeslaPlayer.prototype.open = function (url, meta) {
    var self = this;
    this.close();                     // never two pipelines at once
    this.gen++;
    var gen = this.gen;

    var s = {
      url: url, meta: meta || {}, t0: Date.now(),
      fileMode: !!(meta && meta.fileUrl), fileDone: false, extractStopped: false,
      videoOnly: !!(meta && meta.videoOnly), live: !!(meta && meta.live),
      externalClock: this.externalClock || null,
      base: url, segs: [], cursor: 0, lastUrl: null,
      target: 4, edgeLen: 0,
      tm: null, mbox: null, filePos: 0, initFed: false,
      vTrack: null, aTrack: null,
      vdec: null, adec: null,
      fq: [], pend: [], aPend: [],
      vT0: -1, mediaEnd: 0, frameIv: 0, lastFrameDue: -1,
      paintTimer: null, pumpTimer: null, rafId: 0, statsTimer: 0,
      stopped: false, fatal: null, firstFrameAt: 0,
      paused: false, pausedAt: 0, ended: false, renderPaused: false,
      startAt: (meta && meta.startAt) || 0, startOffset: 0, maxPlayed: 0,
      // Fixed, and deliberately generous. These hold the WORST-CASE read-ahead:
      // three minutes of VOD plus one segment of overshoot, at 60fps and 48kHz.
      // They are NOT derived from the measured frame rate. An earlier version
      // sized them from a running average of the frame intervals, and one
      // outlier timestamp was enough to shrink the cap below a single segment's
      // worth of samples - at which point the queue overflowed on every segment
      // and dropped the oldest entries, which are the frames about to be shown.
      // A fixed cap cannot have that failure mode.
      caps: { fq: 40, v: MAX_VIDEO_BUFFER_SAMPLES, a: MAX_AUDIO_BUFFER_FRAMES },
      ivWin: [],
      aOutRms: 0,
      // counters
      drawn: 0, drops: 0, segsFetched: 0, samples: 0, frames: 0,
      aFrames: 0, aSeconds: 0, aUnderruns: 0, aQueue: 0, aRms: 0,
      // A/V sync: aPrimed marks the one-time drop of already-due audio when
      // joining live, aDepth is the smoothed ring depth the trim is computed
      // from, and aTrim is the correction last sent to the ring.
      aPrimed: false, aDepth: 0, aTrim: 1, lastTrimAt: 0,
      codec: '-', width: 0, height: 0, srcRate: 0,
      decFps: 0, paintFps: 0, lastDecT: 0, lastPaintT: 0,
      gaps: [], lastGapAt: 0, buffered: 0
    };
    this.live = s;
    this.emit('state', this.state());

    var miss = missingLibs(!s.videoOnly);
    if (miss.length) { this.fail('needs ' + miss.join(', ')); return Promise.resolve(false); }

    if (s.videoOnly) this.load(s, gen);
    else this.unlock().then(function () { return self.load(s, gen); });
    return Promise.resolve(true);
  };

  // Pause and resume. The pipeline keeps its decoders open; pausing suspends
  // the audio context and freezes the media clock so that frames decoded after
  // the pause are not considered late on resume.
  TeslaPlayer.prototype.pause = function () {
    var s = this.live;
    if (!s || s.paused || s.ended) return;
    s.paused = true;
    s.pausedAt = Date.now();
    if (this.actx && this.actx.state === 'running') this.actx.suspend().catch(function () {});
    this.emit('pause');
  };

  TeslaPlayer.prototype.resume = function () {
    var s = this.live;
    if (!s || !s.paused) return;
    var dt = Date.now() - (s.pausedAt || Date.now());
    s.vT0 += dt;
    s.paused = false;
    if (this.actx && this.actx.state === 'suspended') this.actx.resume().catch(function () {});
    this.emit('play');
  };

  TeslaPlayer.prototype.play = function () {
    this.resume();
  };

  TeslaPlayer.prototype.isPaused = function () {
    return !!(this.live && this.live.paused);
  };

  TeslaPlayer.prototype.syncTo = function (seconds) {
    var s = this.live;
    if (!s || s.vT0 < 0 || !isFinite(seconds)) return;
    var relative = Math.max(0, seconds - (s.startOffset || 0));
    var wanted = Date.now() - relative * 1000;
    var delta = wanted - s.vT0;
    if (Math.abs(delta) > 35) {
      s.vT0 = wanted;
      for (var i = 0; i < s.pend.length; i++) s.pend[i].due += delta;
      for (var j = 0; j < s.fq.length; j++) s.fq[j].due += delta;
      if (s.lastFrameDue >= 0) s.lastFrameDue += delta;
      if (s.paintTimer) clearTimeout(s.paintTimer);
      s.paintTimer = null;
      this.schedulePaint(s, this.gen);
    }
  };

  TeslaPlayer.prototype.setClock = function (clock) {
    this.externalClock = typeof clock === 'function' ? clock : null;
    if (this.live) this.live.externalClock = this.externalClock;
  };

  TeslaPlayer.prototype.setVideoPaused = function (paused) {
    if (this.live) this.live.renderPaused = !!paused;
  };

  TeslaPlayer.prototype.catchUp = function (targetSeconds) {
    var s = this.live;
    if (!s || s.vT0 < 0) return;
    var target = Number(targetSeconds);
    if (!isFinite(target)) return;
    while (s.fq.length && target - s.fq[0].time > 0.12) {
      try { s.fq.shift().frame.close(); } catch (e) {}
      s.drops++;
    }
    while (s.pend.length && s.pend[0].due < Date.now() - 250) {
      s.pend.shift();
      s.drops++;
    }
    if (!s.paintTimer) this.schedulePaint(s, this.gen);
  };

  TeslaPlayer.prototype.load = function (s, gen) {
    var self = this;
    if (s.fileMode) return this.loadFile(s, gen);
    return this.loadPlaylist(s, gen).then(function () {
      if (s.stopped || self.gen !== gen) return;
      // Join several segments back from the edge for live. A VOD playlist is a
      // fixed list: start at the segment containing the requested offset.
      if (s.vod) {
        var t = 0, idx = 0;
        for (; idx < s.segs.length; idx++) {
          if (t + s.segs[idx].dur > s.startAt) break;
          t += s.segs[idx].dur;
        }
        s.cursor = Math.min(idx, Math.max(0, s.segs.length - 1));
        // The first frame in each YouTube HLS segment uses a segment-local
        // timestamp, so report the segment's absolute start as the clock base.
        s.startOffset = t;
      } else {
        s.cursor = liveStartIndex(s.segs);
      }
      self.startMux(s, gen);
    }).catch(function (e) { self.fail('playlist: ' + e.message); });
  };

  // Progressive MP4 fallback. Tesla/Chrome still gets the same canvas/WebCodecs
  // presentation path; the file is demuxed directly by mp4box rather than sent
  // through an HTMLVideoElement. This is intended for the smaller muxed MP4
  // streams returned when no HLS manifest is available.
  TeslaPlayer.prototype.loadFile = function (s, gen) {
    var self = this;
    s.vod = true;
    s.mbox = MP4Box.createFile();
    this.startMux(s, gen);
    return fetch(s.url, { cache: 'no-store', priority: 'high' }).then(function (r) {
      if (!r.ok) throw new Error('HTTP ' + r.status);
      return r.arrayBuffer();
    }).then(function (buf) {
      if (s.stopped || self.gen !== gen) return;
      self.feedMp4(s, new Uint8Array(buf));
      try { s.mbox.flush(); } catch (e) {}
      var info = null;
      try { info = s.mbox.getInfo(); } catch (e) {}
      if (info && info.duration && info.timescale) s.edgeLen = info.duration / info.timescale;
      if (info && info.videoTracks && info.videoTracks[0] && info.videoTracks[0].nb_samples) {
        s.caps.v = Math.max(s.caps.v, info.videoTracks[0].nb_samples + 16);
      }
      if (info && info.audioTracks && info.audioTracks[0] && info.audioTracks[0].nb_samples) {
        s.caps.a = Math.max(s.caps.a, info.audioTracks[0].nb_samples + 16);
      }
      if (!s.vTrack) self.setupTracks(s);
      s.fileDone = true;
    }).catch(function (e) { self.fail('file: ' + e.message); });
  };

  // Fetch the playlist, following a master playlist to its best variant.
  TeslaPlayer.prototype.loadPlaylist = function (s, gen) {
    var self = this;
    return fetch(s.url, { cache: 'no-store', priority: 'high' }).then(function (r) {
      if (!r.ok) throw new Error('HTTP ' + r.status);
      // The starlite URL 301s to a per-session CDN host; segment paths are
      // relative to THAT, not to the URL we asked for. Resolving against the
      // original yields "Resource not found" for every segment.
      var finalUrl = r.url || s.url;
      return r.text().then(function (t) { return { text: t, finalUrl: finalUrl }; });
    }).then(function (o) {
      if (s.stopped || self.gen !== gen) return null;
      var text = o.text, base = o.finalUrl;
      // A master playlist lists variants with #EXT-X-STREAM-INF and has no
      // segments of its own. F1TV is one. Pick the highest bandwidth variant:
      // the car can take it, and picking by bandwidth is more predictable than
      // guessing from a RESOLUTION attribute.
      var variant = pickVariant(text, base, self.opts.maxHeight || 0);
      if (variant) {
        s.base = variant;
        s.master = true;
        s.aUrl = s.videoOnly ? null : pickAudio(text, base);
        return fetch(variant, { cache: 'no-store', priority: 'high' }).then(function (r2) {
          if (!r2.ok) throw new Error('variant HTTP ' + r2.status);
          var f2 = r2.url || variant;
          return r2.text().then(function (t2) { return { text: t2, finalUrl: f2 }; });
        });
      }
      return { text: text, finalUrl: base };
    }).then(function (o) {
      if (s.stopped || self.gen !== gen || !o) return;
      s.base = o.finalUrl;
      var p = parsePlaylist(o.text);
      if (!p.segs.length) throw new Error('no segments in playlist');
      s.target = p.target;
      s.segs = p.segs;
      s.map = p.map;
      s.vod = !!p.vod;
      s.edgeLen = p.segs.reduce(function (a, x) { return a + x.dur; }, 0);
      s.segDur = p.segs.length ? p.segs[0].dur : 4;
      if (s.aUrl) {
        return fetch(s.aUrl, { cache: 'no-store', priority: 'high' }).then(function (r3) {
          if (!r3.ok) throw new Error('audio HTTP ' + r3.status);
          var f3 = r3.url || s.aUrl;
          return r3.text().then(function (t3) { return { text: t3, finalUrl: f3 }; });
        }).then(function (ao) {
          var ap = parsePlaylist(ao.text);
          s.aBase = ao.finalUrl;
          s.aSegs = ap.segs;
          s.aMap = ap.map;
          s.aVod = !!ap.vod;
        }).catch(function () { s.aUrl = null; });
      }
    });
  };

  // The first DEFAULT audio rendition, or the first audio rendition. YouTube's
  // HLS variants carry video only; the sound lives in a separate playlist.
  function pickAudio(text, base) {
    var lines = text.split(/\r?\n/);
    var fallback = null;
    for (var i = 0; i < lines.length; i++) {
      var line = lines[i].trim();
      if (line.indexOf('#EXT-X-MEDIA:') !== 0 || line.indexOf('TYPE=AUDIO') < 0) continue;
      var m = /URI="([^"]+)"/.exec(line);
      if (!m) continue;
      var url = absolute(m[1], base);
      if (/original/i.test(line)) return url;
      if (/DEFAULT=YES/.test(line)) return url;
      if (!fallback) fallback = url;
    }
    return fallback;
  }

  // Highest-bandwidth variant, or null when this is already a media playlist.
  function pickVariant(text, base, maxHeight) {
    var lines = text.split(/\r?\n/);
    var best = null, bestBw = -1, pending = null;
    var fallback = null, fallbackBw = -1;
    for (var i = 0; i < lines.length; i++) {
      var line = lines[i].trim();
      if (line.indexOf('#EXT-X-STREAM-INF:') === 0) {
        pending = line;
      } else if (line && line.charAt(0) !== '#' && pending) {
        var bw = /BANDWIDTH=(\d+)/.exec(pending);
        var w = bw ? parseInt(bw[1], 10) : 0;
        var res = /RESOLUTION=\d+x(\d+)/.exec(pending);
        var h = res ? parseInt(res[1], 10) : 0;
        if (w > fallbackBw) { fallbackBw = w; fallback = line; }
        if (!maxHeight || !h || h <= maxHeight) {
          if (w > bestBw) { bestBw = w; best = line; }
        }
        pending = null;
      } else if (line && line.charAt(0) !== '#') {
        // A segment with no preceding STREAM-INF: this is a media playlist.
        return null;
      }
    }
    if (!best) best = fallback;
    return best ? absolute(best, base) : null;
  }

  function absolute(u, base) {
    try { return new URL(u, base).href; } catch (e) { return u; }
  }

  function parsePlaylist(text) {    var segs = [], dur = 0, target = 4, map = null, vod = false;
    var lines = text.split(/\r?\n/);
    for (var i = 0; i < lines.length; i++) {
      var line = lines[i].trim();
      if (!line) continue;
      if (line.indexOf('#EXT-X-TARGETDURATION:') === 0) {
        target = parseFloat(line.slice(21)) || target;
      } else if (line.indexOf('#EXT-X-PLAYLIST-TYPE:VOD') === 0) {
        vod = true;
      } else if (line.indexOf('#EXT-X-ENDLIST') === 0) {
        vod = true;
      } else if (line.indexOf('#EXT-X-MAP:') === 0) {
        var mu = /URI="([^"]+)"/.exec(line);
        if (mu) map = mu[1];
      } else if (line.indexOf('#EXTINF:') === 0) {
        dur = parseFloat(line.slice(8));
      } else if (line.charAt(0) !== '#') {
        segs.push({ url: line, dur: dur || target });
        dur = 0;
      }
    }
    return { segs: segs, target: target, map: map, vod: vod };
  }

  // Raw ADTS AAC, as YouTube's HLS audio renditions are packaged. WebCodecs
  // accepts ADTS input when no AudioSpecificConfig description is supplied.
  function adtsConfig(bytes) {
    if (!bytes || bytes.length < 7) return null;
    if (bytes[0] !== 0xFF || (bytes[1] & 0xF0) !== 0xF0) return null;
    var rates = [96000, 88200, 64000, 48000, 44100, 32000, 24000, 22050, 16000, 12000, 11025, 8000, 7350];
    var sampleIndex = (bytes[2] >> 2) & 0xF;
    if (sampleIndex >= rates.length) return null;
    var profile = (bytes[2] >> 6) & 3;
    var objectType = profile + 1;
    var channelConfig = ((bytes[2] & 1) << 2) | ((bytes[3] >> 6) & 3);
    var channels = channelConfig || 2;
    var description = new Uint8Array([
      (objectType << 3) | (sampleIndex >> 1),
      ((sampleIndex & 1) << 7) | (channels << 3)
    ]);
    return { rate: rates[sampleIndex], channels: channels, description: description };
  }

  function adtsFrames(bytes) {
    var frames = [], i = 0;
    while (i + 7 <= bytes.length) {
      if (bytes[i] !== 0xFF || (bytes[i + 1] & 0xF0) !== 0xF0) { i++; continue; }
      var len = ((bytes[i + 3] & 3) << 11) | (bytes[i + 4] << 3) | (bytes[i + 5] >> 5);
      var headerLen = (bytes[i + 1] & 1) ? 7 : 9;
      if (len < headerLen || i + len > bytes.length) break;
      frames.push(bytes.subarray(i + headerLen, i + len));
      i += len;
    }
    return frames;
  }

  function stripId3(bytes) {
    var offset = 0;
    while (bytes.length - offset > 10 &&
           bytes[offset] === 0x49 && bytes[offset + 1] === 0x44 && bytes[offset + 2] === 0x33) {
      var size = ((bytes[offset + 6] & 0x7F) << 21) | ((bytes[offset + 7] & 0x7F) << 14) |
                 ((bytes[offset + 8] & 0x7F) << 7) | (bytes[offset + 9] & 0x7F);
      offset += 10 + size;
    }
    return bytes.subarray(offset);
  }

  // ---- mux setup ----------------------------------------------------------
  TeslaPlayer.prototype.startMux = function (s, gen) {
    var self = this;
    if (!s.mbox) s.mbox = MP4Box.createFile();
    if (!s.fileMode && s.map) {
      // fMP4 HLS (YouTube): the init segment is fetched once and every media
      // segment is already fMP4, so mp4box consumes it directly. The mux.js
      // transmuxer is only needed for MPEG-TS input.
      s.fmp4 = true;
      fetch(absolute(s.map, s.base), { cache: 'no-store', priority: 'high' }).then(function (r) {
        if (!r.ok) throw new Error('init HTTP ' + r.status);
        return r.arrayBuffer();
      }).then(function (buf) {
        if (s.stopped || self.gen !== gen) return;
        s.initFed = true;
        self.feedMp4(s, new Uint8Array(buf));
      }).catch(function (e) { self.fail('init: ' + e.message); });
    } else if (!s.fileMode) {
      s.tm = new muxjs.mp4.Transmuxer({ keepOriginalTimestamps: false, removeEPK: true });

      // mux.js 6 is an EventEmitter. It fires at a SEGMENT BOUNDARY, so segment
      // N's fMP4 only appears once N+1 has been pushed - which is why a single
      // push() produces nothing.
      s.tm.on('data', function (event) {
        if (s.stopped || self.gen !== gen) return;
        // The init segment (ftyp+moov) is fed exactly once. mux.js repeats it on
        // every event, and handing mp4box a second moov makes it rebuild its
        // sample tables against truns it has not seen; appendBuffer then throws
        // and the whole pipeline stops.
        if (event.initSegment && !s.initFed) { s.initFed = true; self.feedMp4(s, new Uint8Array(event.initSegment)); }
        if (event.data) self.feedMp4(s, new Uint8Array(event.data));
      });
    }

    s.vdec = new VideoDecoder({
      output: function (frame) { self.onVideoFrame(s, frame); },
      error: function (e) { self.fail('video decoder: ' + e.message); }
    });

    if (!s.fileMode && !s.videoOnly && s.aMap) {
      s.ambox = MP4Box.createFile();
      fetch(absolute(s.aMap, s.aBase), { cache: 'no-store', priority: 'high' }).then(function (r) {
        if (!r.ok) throw new Error('audio init HTTP ' + r.status);
        return r.arrayBuffer();
      }).then(function (buf) {
        if (s.stopped || self.gen !== gen) return;
        s.aInitFed = true;
        self.feedAudioMp4(s, new Uint8Array(buf));
      }).catch(function (e) { s.aErr = 'audio init: ' + e.message; });
    } else if (s.aUrl) {
      s.aAdts = true;
    }

    s.pumpTimer = setInterval(function () {
      if (s.stopped || self.gen !== gen) return;
      self.feedDecoders(s, Date.now());
    }, 10);
    // The pump is a self-rescheduling loop rather than a tight while, so closing
    // a channel mid-fetch cannot leave an orphaned loop running.
    if (!s.fileMode) self.pump(s, gen);
    self.schedulePaint(s, gen);

    s.statsTimer = setInterval(function () {
      if (s.stopped || self.gen !== gen) return;
      self.emit('state', self.state());
    }, 500);
  };

  TeslaPlayer.prototype.feedMp4 = function (s, bytes) {
    if (!s.mbox || s.stopped) return;
    try {
      var ab = bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
      ab.fileStart = s.filePos;
      s.mbox.appendBuffer(ab);
      s.filePos += ab.byteLength;
      if (!s.vTrack && !s.fileMode) this.setupTracks(s);
    } catch (e) { this.fail('demux: ' + e.message); }
  };

  TeslaPlayer.prototype.feedAudioMp4 = function (s, bytes) {
    if (!s.ambox || s.stopped) return;
    try {
      var ab = bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
      ab.fileStart = s.afilePos;
      s.ambox.appendBuffer(ab);
      s.afilePos += ab.byteLength;
      if (!s.aTrack) this.setupAudioTrack(s);
    } catch (e) { s.aErr = 'audio demux: ' + e.message; }
  };

  TeslaPlayer.prototype.setupAudioTrack = function (s) {
    var self = this;
    var info;
    try { info = s.ambox.getInfo(); } catch (e) { return; }
    if (!info) return;
    var ats = info.audioTracks || [];
    if (!ats.length) return;
    s.aTrack = ats[0];
    try {
      this.setupAudio(s, s.ambox.getTrackById(s.aTrack.id));
    } catch (e) { s.aErr = 'audio config: ' + e.message; return; }
    s.ambox.setExtractionOptions(s.aTrack.id, null, { nbSamples: 200 });
    s.ambox.onSamples = function (id, user, samples) { self.onAudioSamples(s, samples); };
    s.ambox.start();
  };

  TeslaPlayer.prototype.onAudioSamples = function (s, samples) {
    s.samples += samples.length;
    var first = true;
    for (var i = 0; i < samples.length; i++) {
      var sm = samples[i];
      if (!sm || !sm.data || !sm.data.byteLength) continue;
      var raw = new Uint8Array(sm.data.buffer.slice(sm.data.byteOffset, sm.data.byteOffset + sm.data.byteLength));
      var sync = !!sm.is_sync || first;
      first = false;
      if (s.aTrack && s.adec) {
        var as = (s.aTrack.timescale || 48000);
        var asec = sm.cts / as;
        s.aPend.push({ sync: sync, ts: Math.round(asec * 1e6), raw: raw });
      }
    }
    while (s.aPend.length > s.caps.a) { s.aPend.shift(); s.drops++; }
  };

  TeslaPlayer.prototype.feedAdtsAudio = function (s, raw) {
    if (s.stopped) return;
    var bytes = stripId3(raw);
    if (!s.adec) {
      var cfg = adtsConfig(bytes);
      if (!cfg) return;
      s.srcRate = cfg.rate;
      s.aTrack = { timescale: cfg.rate };
      s.adec = new AudioDecoder({
        output: (function (self) {
          return function (data) { self.queueAudio(s, data); data.close(); };
        })(this),
        error: (function (self) {
          return function (e) { s.aErr = 'audio decoder: ' + (e && e.message); s.adec = null; };
        })(this)
      });
      try {
        s.adec.configure({
          codec: 'mp4a.40.2',
          sampleRate: cfg.rate,
          numberOfChannels: cfg.channels,
          description: cfg.description
        });
      } catch (e) {
        s.aErr = 'audio config: ' + e.message;
        s.adec = null;
        return;
      }
      this.ensureAudio(cfg.rate);
      s.aTime = s.aTime || 0;
    }
    var frames = adtsFrames(bytes);
    for (var i = 0; i < frames.length; i++) {
      s.aPend.push({ sync: true, ts: Math.round((s.aTime || 0) * 1e6), raw: frames[i] });
      s.aTime = (s.aTime || 0) + 1024 / (s.srcRate || 48000);
    }
    while (s.aPend.length > s.caps.a) { s.aPend.shift(); s.drops++; }
  };

  // Pick the real video and audio tracks. getInfo() is only a summary; the
  // sample-entry box tree (where avcC and esds live) comes from getTrackById().
  TeslaPlayer.prototype.setupTracks = function (s) {
    var self = this;
    var info;
    try { info = s.mbox.getInfo(); } catch (e) { return; }
    if (!info) return;

    var tracks = (info.videoTracks || []);
    if (!tracks.length) { s.noVideo = (s.noVideo || 0) + 1; return; }
    var vt = tracks[0];
    s.vTrack = vt;

    // Choose the audio track by codec, not by position. F1TV's TS carries
    // scte_35 and timed_id3 beside the real audio; taking the first entry
    // decodes SCTE-35 ad markers as if they were sound.
    var at = null;
    var ats = s.videoOnly ? [] : (info.audioTracks || []);
    for (var i = 0; i < ats.length; i++) {
      var c = (ats[i].codec || '') + ' ' + (ats[i].type || '');
      if (/mp4a|aac/i.test(c)) { at = ats[i]; break; }
      if (!at) at = ats[i];
    }
    s.aTrack = at || null;
    s.audioFromMux = !!s.aTrack;

    var cfg = this.videoConfig(s.mbox.getTrackById(vt.id));
    s.codec = cfg.codec;
    try {
      s.vdec.configure(cfg);
    } catch (e) { this.fail('video config: ' + e.message); return; }

    if (s.aTrack) { try { this.setupAudio(s, s.mbox.getTrackById(s.aTrack.id)); } catch (e) {} }

    if (s.fileMode && s.startAt > 0 && s.mbox.seek) {
      try { s.mbox.seek(s.startAt, true); } catch (e) {}
    }
    s.mbox.setExtractionOptions(vt.id, null, { nbSamples: 90 });
    if (s.aTrack) s.mbox.setExtractionOptions(s.aTrack.id, null, { nbSamples: 200 });
    s.mbox.onSamples = function (id, user, samples) { self.onSamples(s, id, samples); };
    s.mbox.start();   // without start() mp4box never releases samples
  };

  TeslaPlayer.prototype.videoConfig = function (trak) {
    var entry = trak.mdia.minf.stbl.stsd.entries[0];
    var desc = avcCDescription(entry && entry.avcC);
    var codec = trak.codec || (entry && entry.avcC
      ? 'avc1.' + hex2(entry.avcC.AVCProfileIndication) + hex2(entry.avcC.profile_compatibility) + hex2(entry.avcC.AVCLevelIndication)
      : 'avc1.64001f');
    var cfg = { codec: codec, optimizeForLatency: true, hardwareAcceleration: 'prefer-hardware' };
    if (desc) cfg.description = desc;
    return cfg;
  };

  // ---- audio --------------------------------------------------------------
  // The audio graph is owned by the PLAYER, not by a stream. It is built once
  // and shared across every channel, and only the decoder feeding it changes.
  //
  // Building it per channel was a real bug: each switch created another
  // AudioWorkletNode, gain, limiter and analyser, and re-ran addModule for the
  // same processor name. Flick through a few channels and you have a stack of
  // live audio chains fighting over the output.
  TeslaPlayer.prototype.setupAudio = function (s, trak) {
    var self = this;
    if (!this.actx) return;
    var entry = trak.mdia.minf.stbl.stsd.entries[0];
    var desc = ascFromEsds(entry && entry.esds);

    // The sample rate comes from the stream, and it has to be read from the
    // right place. Two things bite here:
    //   - the sample entry's field is `samplerate`, all lowercase, and it is
    //     16.16 FIXED POINT in a uint32, so 48000 arrives as 3145728000;
    //   - the audio TRACK's timescale is the sample rate directly (32000 on
    //     nasa.4k.us, 48000 on the rest), which is the reliable source.
    // Getting this wrong configures the decoder for a rate the data is not,
    // and the channel comes up with a perfect picture and no sound at all.
    var rate = 0;
    if (s.aTrack && s.aTrack.timescale) rate = s.aTrack.timescale;
    if (!rate && entry) {
      var raw = entry.samplerate || entry.samplingRate || 0;
      if (raw > 65536) rate = Math.round(raw / 65536);
      else if (raw) rate = raw;
    }
    if (!rate) rate = (this.actx && this.actx.sampleRate) || 48000;
    s.srcRate = rate;
    // Real channel count too, rather than assuming stereo.
    s.srcCh = (entry && (entry.channel_count || entry.channelCount)) || 2;

    s.adec = new AudioDecoder({
      output: function (data) { self.queueAudio(s, data); data.close(); },
      error: function (e) { s.aErr = 'audio decoder: ' + (e && e.message); s.adec = null; }
    });
    var cfg = { codec: 'mp4a.40.2', sampleRate: s.srcRate, numberOfChannels: s.srcCh };
    if (desc) cfg.description = desc;
    try { s.adec.configure(cfg); } catch (e) { s.aErr = 'audio config: ' + e.message; s.adec = null; return; }
    this.ensureAudio(s.srcRate);
  };

  // Build the ring and its output chain. Idempotent, and shared by every
  // channel. sourceRate tells the ring the stream's rate so it can resample to
  // the device's; channels differ (32kHz vs 48kHz), so it is set per channel.
  TeslaPlayer.prototype.ensureAudio = function (sourceRate) {
    var a = this.audio;
    if (sourceRate) a.sourceRate = sourceRate;
    if (!this.actx) return Promise.resolve(false);
    if (a.ready) { this.setAudioRate(a.sourceRate); return Promise.resolve(true); }
    if (a.pending) return a.pending;
    a.pending = true;
    var self = this, ctx = this.actx;
    var urls = [
      URL.createObjectURL(new Blob([RING_WORKLET], { type: 'application/javascript' })),
      'data:application/javascript;base64,' + btoa(RING_WORKLET)
    ];
    var tryUrl = function (i) {
      if (i >= urls.length) { useScriptProcessor(); return; }
      ctx.audioWorklet.addModule(urls[i]).then(function () {
        wire();
      }).catch(function (e) {
        // Record the refusal rather than swallowing it: a refused module used
        // to leave the page with a perfect picture and no sound at all, with
        // nothing on screen to say why.
        a.modErr += ' [' + (i ? 'data' : 'blob') + ': ' + (e && e.message) + ']';
        tryUrl(i + 1);
      });
    };
    tryUrl(0);

    function wire() {
      a.node = new AudioWorkletNode(ctx, 'lofi-ring', {
        numberOfInputs: 0, numberOfOutputs: 1, outputChannelCount: [2],
        processorOptions: { capacity: Math.max(48000 * 8, ctx.sampleRate * 8),
                            sourceRate: a.sourceRate || ctx.sampleRate }
      });
      a.node.port.onmessage = function (e) {
        var d = e.data || {};
        if (typeof d.depth === 'number') a.depth = d.depth;
        if (typeof d.rms === 'number') a.rms = d.rms;
        if (d.starved) a.underruns = d.underruns;
      };
      a.push = function (planes) { a.node.port.postMessage(planes); };
      a.setRate = function (r) { a.node.port.postMessage({ rate: r }); };
      // 1 = the stream's own rate; the sync loop nudges it either side.
      a.setTrim = function (x) { a.node.port.postMessage({ trim: x }); };
      finish(a.node);
      a.path = 'AudioWorklet';
    }

    // Last resort: the same ring, pulled by a ScriptProcessorNode. Deprecated,
    // but it is a built-in node type - no module loading, no blob URL, so
    // nothing can block it the way a CSP blocks addModule(). It resamples from
    // the stream's rate to the device's, for the same reason the worklet does.
    function useScriptProcessor() {
      try {
        var sp = ctx.createScriptProcessor(2048, 1, 2);
        var cap = Math.max(48000 * 8, ctx.sampleRate * 8);
        var ch = [new Float32Array(cap), new Float32Array(cap)];
        var st = { w: 0, pos: 0, avail: 0, fed: false, under: 0, trim: 1, srcRate: a.sourceRate || ctx.sampleRate };
        st.step = st.srcRate / ctx.sampleRate;
        sp.onaudioprocess = function (ev) {
          var out = ev.outputBuffer, n = out.length, starved = false;
          var stp = st.step * st.trim;
          for (var i = 0; i < n; i++) {
            var l = 0, rr = 0;
            if (st.avail >= 1) {
              var i0 = st.pos | 0, i1 = i0 + 1, f = st.pos - i0;
              var a0 = i0 % cap, a1 = i1 % cap;
              if (f > 0) {
                l = ch[0][a0] + (ch[0][a1] - ch[0][a0]) * f;
                rr = ch[1][a0] + (ch[1][a1] - ch[1][a0]) * f;
              } else { l = ch[0][a0]; rr = ch[1][a0]; }
              st.pos += stp; st.avail -= stp;
            } else starved = true;
            out.getChannelData(0)[i] = l;
            if (out.numberOfChannels > 1) out.getChannelData(1)[i] = rr;
          }
          if (starved && st.fed) { st.under++; a.underruns = st.under; }
          a.depth = st.avail / st.srcRate;
        };
        a.push = function (planes) {
          var n = planes[0].length;
          if (st.avail + n > cap) {
            var room = Math.max(0, cap - st.avail);
            for (var i = 0; i < room; i++) {
              ch[0][st.w] = planes[0][i]; ch[1][st.w] = planes[1][i]; st.w = (st.w + 1) % cap;
            }
            st.avail += room;
            return;
          }
          for (var j = 0; j < n; j++) {
            ch[0][st.w] = planes[0][j]; ch[1][st.w] = planes[1][j]; st.w = (st.w + 1) % cap;
          }
          st.avail += n; st.fed = true;
        };
        a.setRate = function (r) {
          st.srcRate = r; st.step = r / ctx.sampleRate;
          st.w = 0; st.pos = 0; st.avail = 0; st.fed = false;
        };
        a.setTrim = function (x) { st.trim = x; };
        a.flush = function () { st.w = 0; st.pos = 0; st.avail = 0; st.fed = false; };
        a.node = sp;
        finish(sp);
        a.path = 'ScriptProcessor (fallback)';
      } catch (e) {
        a.path = 'unavailable';
        a.modErr += ' [sproc: ' + e.message + ']';
        a.pending = false;
      }
    }

    function finish(node) {
      // gain -> limiter -> analyser -> destination.
      // The source is quiet (about -30dB mean on these feeds, against roughly
      // -20dB for normal broadcast), so it is lifted back to programme level.
      // The limiter is what stops peaks that were already near -10dB from
      // clipping once they are amplified.
      var g = ctx.createGain();
      g.gain.value = self.muted ? 0 : self.gainValue;
      var lim = ctx.createDynamicsCompressor();
      lim.threshold.value = -6; lim.knee.value = 6; lim.ratio.value = 12;
      lim.attack.value = 0.003; lim.release.value = 0.25;
      var an = ctx.createAnalyser();
      an.fftSize = 2048;
      node.connect(g); g.connect(lim); lim.connect(an); an.connect(ctx.destination);
      a.gain = g; a.limiter = lim; a.analyser = an; a.buf = new Float32Array(2048);
      a.ready = true; a.pending = false;
      if (ctx.state === 'suspended') ctx.resume().catch(function () {});
      a.pending = Promise.resolve(true);
    }
    return a.pending;
  };

  // Tell the ring which rate the incoming samples are in. Sent when a channel
  // opens, because channels differ: the ring drains at the device's rate, so a
  // mismatch starves it continuously.
  TeslaPlayer.prototype.setAudioRate = function (r) {
    var a = this.audio;
    if (!r || a.rate === r) return;
    a.rate = r;
    if (a.setRate) a.setRate(r);
  };

  // Mute by zeroing the gain node the volume already runs through, rather than
  // by tearing the audio graph down. Two reasons: the picture must keep
  // running while muted, and the ring keeps filling, so unmuting is instant
  // instead of starting again on a starved buffer.
  TeslaPlayer.prototype.setMuted = function (on) {
    this.muted = !!on;
    var a = this.audio;
    if (a.gain && this.actx) {
      var target = this.muted ? 0 : this.gainValue;
      try {
        var t = this.actx.currentTime;
        // Ramped, not stepped: snapping the gain to zero clicks on anything
        // with content above the noise floor.
        a.gain.gain.cancelScheduledValues(t);
        a.gain.gain.setValueAtTime(a.gain.gain.value, t);
        a.gain.gain.linearRampToValueAtTime(target, t + 0.04);
      } catch (e) {
        a.gain.gain.value = target;
      }
    }
    return this.muted;
  };

  // ---- audio/video sync ---------------------------------------------------
  // Audio is decoded AUDIO_LEAD_S ahead of its due time and poured into a ring
  // the device drains; the picture is painted against the system clock at each
  // frame's due time. The two agree only when the ring holds exactly the decode
  // lead, because the lead and the buffered depth cancel each other - so the
  // depth of the ring IS the sync error, and it is the one number this needs.
  //
  // Any drift between the audio device's clock and the system clock (there is
  // always some) pushes the depth off that target and slides the sound against
  // the picture. The correction is to resample the ring read by a fraction of
  // a percent: faster when the ring is too deep, slower when it is too shallow.
  // That is inaudible where dropping or repeating samples to catch up clicks,
  // and unlike moving the video clock it does not need to know which of the two
  // clocks is the correct one.
  var TRIM_MAX = 0.02;       // never shift pitch by more than 2%
  // A proportional gain, sized so a realistic clock error asks for a tiny
  // correction. 0.25 leaves a 20ms residual for an extreme 0.5% clock error
  // and well under 2ms for the 50-200ppm an ordinary device shows, which is
  // far below the ~40ms where a lip-sync offset starts to be visible. It is
  // also far enough from the 400ms resend interval to keep the loop stable.
  var TRIM_GAIN = 0.25;
  var TRIM_DEADBAND = 0.0005;

  TeslaPlayer.prototype.trimAudio = function (s, now) {
    var a = this.audio;
    if (!a.ready || !a.setTrim) return;
    // Smooth the depth before treating it as an error: the worklet reports it
    // once per process block and the decoder delivers in bursts, so a single
    // reading is noise. Seeded from the first non-zero reading because a ring
    // that is still filling is legitimately empty, not "audio is early".
    s.aDepth = s.aDepth ? s.aDepth * 0.85 + a.depth * 0.15 : a.depth;
    var f = (s.aDepth - AUDIO_LEAD_S) * TRIM_GAIN;
    if (f > TRIM_MAX) f = TRIM_MAX; else if (f < -TRIM_MAX) f = -TRIM_MAX;
    if (Math.abs(f) < TRIM_DEADBAND) f = 0;
    this.setAudioTrim(s, 1 + f, now);
  };

  // Sending on every 10ms tick would flood the audio thread for no gain - the
  // ring moves far slower than that. Send only when the correction has moved
  // enough to matter, and at most a few times a second otherwise.
  TeslaPlayer.prototype.setAudioTrim = function (s, trim, now) {
    if (s.aTrim === trim) return;
    if (now - (s.lastTrimAt || 0) < 400 && Math.abs(trim - s.aTrim) < 0.002) return;
    s.aTrim = trim;
    s.lastTrimAt = now;
    this.audio.trim = trim;
    try { this.audio.setTrim(trim); } catch (e) {}
  };

  // Drop whatever the previous channel left in the ring, so a switch does not
  // play out the tail of the old one.
  TeslaPlayer.prototype.flushAudio = function () {
    var a = this.audio;
    if (a.flush) a.flush();
    else if (a.node && a.node.port) { try { a.node.port.postMessage({ flush: 1 }); } catch (e) {} }
    a.underruns = 0; a.depth = 0;
    // Sound the next channel at its own rate. A trim left over from the last
    // one would be invisible to the new stream (its sync state starts at 1)
    // and would run the ring off-cadence until the loop noticed.
    a.trim = 1;
    if (a.setTrim) { try { a.setTrim(1); } catch (e) {} }
  };

  TeslaPlayer.prototype.queueAudio = function (s, data) {
    if (s.stopped) return;
    var a = this.audio;
    if (!a.ready || !a.push) return;
    // The decoder's output rate can differ from the container/track rate
    // (HE-AAC/SBR). The ring must resample from what is actually output, not
    // from the declared rate, or playback runs at the wrong speed.
    if (data.sampleRate && a.sourceRate !== data.sampleRate) {
      a.sourceRate = data.sampleRate;
      this.setAudioRate(data.sampleRate);
    }
    var n = data.numberOfFrames;
    var planes = [new Float32Array(n), new Float32Array(n)];
    var nch = data.numberOfChannels || 1;
    for (var c = 0; c < 2; c++) {
      data.copyTo(planes[c], { planeIndex: c < nch ? c : 0, format: 'f32-planar' });
    }
    a.push(planes);
    s.aFrames++;
    // Counted in the track's own timebase, so a 32kHz channel reports seconds
    // rather than being read as if it were 48kHz.
    s.aSeconds += n / (data.sampleRate || s.srcRate || 48000);
  };

  // ---- samples ------------------------------------------------------------
  TeslaPlayer.prototype.onSamples = function (s, id, samples) {
    s.samples += samples.length;
    // Every append begins at a segment boundary, and HLS segments open with a
    // keyframe even when the packager omits mp4box's is_sync flags. Without
    // this the decoder key-waits and stalls.
    var first = true;
    for (var i = 0; i < samples.length; i++) {
      var sm = samples[i];
      if (!sm || !sm.data || !sm.data.byteLength) continue;
      var raw = new Uint8Array(sm.data.buffer.slice(sm.data.byteOffset, sm.data.byteOffset + sm.data.byteLength));
      var sync = !!sm.is_sync || (!s.fileMode && first);
      first = false;
      if (s.vTrack && id === s.vTrack.id) {
        var vs = (s.vTrack.timescale || 90000);
        var sec = sm.cts / vs;
        // Anchor the media clock so the first frame is due right now. Joining
        // mid-stream means the timestamps already read tens of seconds; anchored
        // at t=0 every frame would be due 40s in the future and nothing would
        // ever decode.
        if (s.vT0 < 0) s.vT0 = Date.now() - sec * 1000;
        if (sec > s.mediaEnd) s.mediaEnd = sec;
        s.pend.push({ sync: sync, ts: Math.round(sec * 1e6), due: s.vT0 + sec * 1000, raw: raw });
      } else if (s.aTrack && s.adec && id === s.aTrack.id) {
        // Audio gets its own queue, paced on the same media clock. Sharing the
        // video queue lets audio evict video - AAC frames outnumber video ~2:1 -
        // and feeding it unpaced delivers a whole segment in one burst, which
        // runs the scheduler far ahead of the audio clock and stutters.
        var as = (s.aTrack.timescale || 48000);
        var asec = sm.cts / as;
        // No due time yet: vT0 may not exist if this track was demuxed before
        // the first video sample. feedDecoders() computes it against whichever
        // anchor exists by the time the sample is released.
        s.aPend.push({ sync: sync, ts: Math.round(asec * 1e6), raw: raw });
      }
    }
    if (s.fileMode) {
      // The complete progressive file is already downloaded; retain its
      // encoded samples for paced decoding while releasing mp4box's own copies.
      try {
        if (samples.length) s.mbox.releaseUsedSamples(id, samples[samples.length - 1].number);
      } catch (e) {}
    } else {
      // Cap each queue at the worst-case segment buffer.
      while (s.pend.length > s.caps.v) { s.pend.shift(); s.drops++; }
      while (s.aPend.length > s.caps.a) { s.aPend.shift(); s.drops++; }
    }
  };

  // Seconds of downloaded media ahead of what is playing right now. Negative
  // means we have run past the download and are starved.
  function bufferedOf(s) {
    if (s.vT0 < 0 || !s.mediaEnd) return 0;
    return s.mediaEnd - (Date.now() - s.vT0) / 1000;
  }

  // Feed the decoders on the media clock. Handing every sample straight to
  // decode() lets the decoder sprint through a whole segment in milliseconds
  // and dump it at once, so the paint gate almost never finds a frame waiting.
  TeslaPlayer.prototype.feedDecoders = function (s, now) {
    if (!s.vdec || s.vdec.state !== 'configured') return;
    // While paused, keep feeding only up to the instant the pause happened.
    // That leaves the decoder's input contiguous when playback resumes, instead
    // of handing it a delta frame after a multi-second gap (which WebCodecs
    // reports as a decoding error).
    var clock = s.paused && s.pausedAt ? s.pausedAt : now;
    while (s.pend.length && s.pend[0].due < clock - 500) { s.pend.shift(); s.drops++; }
    while (s.pend.length && s.pend[0].due - clock < 250) {
      if (s.vdec.decodeQueueSize > 6) break;
      var c = s.pend.shift();
      try {
        s.vdec.decode(new EncodedVideoChunk({ type: c.sync ? 'key' : 'delta', timestamp: c.ts, data: c.raw }));
      } catch (e) { /* queue full */ }
    }
    if (s.adec && s.adec.state === 'configured' && s.vT0 >= 0) {
      if (!s.aPrimed && s.aPend.length) {
        while (s.aPend.length && (s.vT0 + s.aPend[0].ts / 1000) <= clock) { s.aPend.shift(); s.drops++; }
        s.aPrimed = true;
      }
      while (s.aPend.length && (s.vT0 + s.aPend[0].ts / 1000) < clock - 500) { s.aPend.shift(); s.drops++; }
      while (s.aPend.length && (s.vT0 + s.aPend[0].ts / 1000) - clock < AUDIO_LEAD_MS) {
        if (s.adec.decodeQueueSize > 40) break;
        var a = s.aPend.shift();
        try {
          s.adec.decode(new EncodedAudioChunk({ type: a.sync ? 'key' : 'delta', timestamp: a.ts, data: a.raw }));
        } catch (e) {}
      }
      if (!s.paused) this.trimAudio(s, clock);
    }
    if (s.fileMode && s.extractStopped &&
        s.pend.length < s.caps.v * 0.4 && s.aPend.length < s.caps.a * 0.4) {
      s.extractStopped = false;
      try { s.mbox.start(); } catch (e) {}
    }
    if (s.fileMode && s.fileDone && !s.ended && !s.extractStopped &&
        !s.pend.length && !s.aPend.length && !s.fq.length && bufferedOf(s) <= 0.1) {
      this.pause();
      s.ended = true;
      this.emit('ended');
    }
  };

  // ---- video frames -------------------------------------------------------
  TeslaPlayer.prototype.onVideoFrame = function (s, frame) {
    if (s.stopped) { try { frame.close(); } catch (e) {} return; }
    s.frames++;
    var sec = (frame.timestamp || 0) / 1e6;
    var due = s.vT0 >= 0 ? s.vT0 + sec * 1000 : 0;
    // A short queue, not a single slot. The decoder runs slightly ahead of the
    // wall clock, so the NEWEST frame is always a few ms in the future; keeping
    // only that one meant every paint check found "not due yet" and nothing was
    // ever shown.
    //
    // The cap has to exceed the decoder's lookahead or the overflow discards
    // the frames that were due next and the picture skips. With a 250ms lead at
    // 60fps that is ~15 frames, so the cap scales with the learned frame rate.
    if (s.lastFrameDue >= 0 && due > s.lastFrameDue) {
      // The source's real frame interval, as a rolling MEDIAN of the gaps
      // between consecutive decoded frames.
      //
      // A plain exponential average is not safe here. One outlier - a
      // timestamp gap across a segment boundary, or a B-frame reordering - pulls
      // the estimate far enough that anything derived from it moves too, and
      // when that something is a queue cap the queue starts shedding the frames
      // it is supposed to be holding. The median ignores outliers by
      // construction, so a single bad gap cannot resize anything.
      var d = due - s.lastFrameDue;
      s.ivWin.push(d);
      if (s.ivWin.length > 60) s.ivWin.shift();
      if (s.ivWin.length > 8) {
        var sorted = s.ivWin.slice().sort(function (a, b) { return a - b; });
        s.frameIv = sorted[sorted.length >> 1];
      }
    }
    s.lastFrameDue = due;
    // HLS timestamps are not guaranteed to start at zero. Normalize against the
    // first decoded frame so the canvas timeline begins with the audio timeline
    // instead of an arbitrary PTS (which made the paint loop wait forever).
    if (s.firstPts == null) s.firstPts = sec;
    s.fq.push({ frame: frame, due: due, time: (s.startOffset || 0) + (sec - s.firstPts) });
    while (s.fq.length > s.caps.fq) { s.fq.shift().frame.close(); s.drops++; }
  };

  // ---- paint --------------------------------------------------------------
  // Painting is driven by a timer aimed at each frame's own due time, not by
  // rAF. rAF only fires about every 16.7ms, so a 25fps source (a frame every
  // 40ms) is always caught at the NEXT rAF after it comes due - a fixed ~10ms
  // late, every frame, forever. That is not judder you can filter out later; it
  // is a 20fps picture no matter what the source says.
  TeslaPlayer.prototype.setupGL = function () {
    try {
      var gl = this.canvas.getContext('webgl2', {
        alpha: false, antialias: false, desynchronized: true, preserveDrawingBuffer: false
      });
      if (!gl) return false;
      var vs = '#version 300 es\nlayout(location=0) in vec2 p; out vec2 uv; void main(){ gl_Position=vec4(p,0.,1.); uv=p*0.5+0.5; }';
      var fs = '#version 300 es\nprecision mediump float; in vec2 uv; uniform vec4 r; uniform sampler2D t; out vec4 o; void main(){ o=texture(t, mix(r.xy,r.zw,uv)); }';
      var mk = function (type, src) {
        var sh = gl.createShader(type);
        gl.shaderSource(sh, src);
        gl.compileShader(sh);
        if (!gl.getShaderParameter(sh, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(sh));
        return sh;
      };
      var program = gl.createProgram();
      gl.attachShader(program, mk(gl.VERTEX_SHADER, vs));
      gl.attachShader(program, mk(gl.FRAGMENT_SHADER, fs));
      gl.linkProgram(program);
      if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(program));
      gl.useProgram(program);
      var buffer = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1, -1, 1, -1, -1, 1, 1, 1]), gl.STATIC_DRAW);
      var loc = gl.getAttribLocation(program, 'p');
      gl.enableVertexAttribArray(loc);
      gl.vertexAttribPointer(loc, 2, gl.FLOAT, false, 0, 0);
      var texture = gl.createTexture();
      gl.bindTexture(gl.TEXTURE_2D, texture);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
      gl.pixelStorei(gl.UNPACK_FLIP_Y_WEBGL, true);
      gl.pixelStorei(gl.UNPACK_PREMULTIPLY_ALPHA_WEBGL, false);
      this.glProgram = program;
      this.glTexture = texture;
      this.glViewport = gl.getUniformLocation(program, 'r');
      this.gl = gl;
      return true;
    } catch (e) {
      this.gl = null;
      return false;
    }
  };

  TeslaPlayer.prototype.drawFrame = function (frame, cw, ch) {
    if (this.gl) {
      var gl = this.gl;
      try {
        gl.viewport(0, 0, cw, ch);
        gl.bindTexture(gl.TEXTURE_2D, this.glTexture);
        gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, frame);
        var fw = frame.displayWidth || frame.codedWidth;
        var fh = frame.displayHeight || frame.codedHeight;
        var fa = fw / fh, ca = cw / ch;
        var u0 = 0, v0 = 0, u1 = 1, v1 = 1;
        if (fa > ca) { var w = ca / fa; u0 = (1 - w) / 2; u1 = 1 - u0; }
        else { var h = fa / ca; v0 = (1 - h) / 2; v1 = 1 - v0; }
        gl.uniform4f(this.glViewport, u0, v0, u1, v1);
        gl.clearColor(0, 0, 0, 1);
        gl.clear(gl.COLOR_BUFFER_BIT);
        gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);
        return true;
      } catch (e) {
        return false;
      }
    }
    if (this.ctx2d) {
      this.ctx2d.drawImage(frame, 0, 0, cw, ch);
      return true;
    }
    return false;
  };

  TeslaPlayer.prototype.schedulePaint = function (s, gen) {
    var self = this;
    if (s.paintTimer || s.stopped) return;
    if (!s.fq.length) {
      s.paintTimer = setTimeout(function () { s.paintTimer = null; self.schedulePaint(s, gen); }, 10);
      return;
    }
    var wait = s.externalClock
      ? Math.max(0, (s.fq[0].time - Number(s.externalClock())) * 1000)
      : Math.max(0, s.fq[0].due - Date.now());
    s.lastWait = wait;
    s.paintTimer = setTimeout(function () {
      s.paintTimer = null;
      if (s.stopped || self.gen !== gen) return;
      self.paintOne(s);
      self.schedulePaint(s, gen);
    }, wait);
  };

  TeslaPlayer.prototype.paintOne = function (s) {
    if (!s.fq.length || s.paused || s.renderPaused) return;
    s.paintCalls = (s.paintCalls || 0) + 1;
    var wall = Date.now();
    if (s.externalClock) {
      var target = Number(s.externalClock());
      if (!isFinite(target)) return;
      // Hard catch-up: never present a frame that is more than 120ms behind
      // the source clock. Without this the canvas can stay frozen on an old
      // frame while audio continues.
      while (s.fq.length && target - s.fq[0].time > 0.12) {
        try { s.fq.shift().frame.close(); } catch (e) {}
        s.drops++;
      }
      if (!s.fq.length) return;
      if (s.fq[0].time > target + 0.06) { s.paintSkips = (s.paintSkips || 0) + 1; return; }
    }
    // Oldest DUE frame, first-in-first-out. Taking the newest discards
    // everything queued before it, which is a silent drop. When an external
    // audio clock is in charge, its gate above is authoritative; the old
    // wall-clock due time would otherwise reject every frame.
    if (!s.externalClock && s.fq[0].due && s.fq[0].due > wall) return;
    var box = s.fq.shift();
    s.lastDrawnTime = box.time;
    var frame = box.frame;
    var w = frame.displayWidth || frame.codedWidth;
    var h = frame.displayHeight || frame.codedHeight;
    if (!w || !h) { try { frame.close(); } catch (e) {} return; }
    s.width = w; s.height = h;
    var scale = this.maxW && w > this.maxW ? this.maxW / w : 1;
    var cw = Math.max(1, Math.round(w * scale));
    var ch = Math.max(1, Math.round(h * scale));
    if (this.canvas.width !== cw || this.canvas.height !== ch) {
      this.canvas.width = cw; this.canvas.height = ch;
    }
    this.drawFrame(frame, cw, ch);
    try { frame.close(); } catch (e) {}
    s.drawn++;
    if (!s.firstFrameAt) s.firstFrameAt = wall;
    if (s.lastGapAt) {
      var gap = wall - s.lastGapAt;
      s.gaps.push(gap);
      if (s.gaps.length > 400) s.gaps.shift();
    }
    s.lastGapAt = wall;
    s.lastPaintT = wall;
    this.updateFps(s, wall);
  };

  TeslaPlayer.prototype.updateFps = function (s, wall) {
    var dt = s.lastDecT ? (wall - s.lastDecT) / 1000 : 0;
    s.decFps = s.decFps ? s.decFps * 0.7 + (1 / dt) * 0.3 : (dt ? 1 / dt : 0);
    s.paintFps = s.paintFps ? s.paintFps * 0.7 + (1 / dt) * 0.3 : (dt ? 1 / dt : 0);
    s.lastDecT = wall;
  };

  // ---- segment pump -------------------------------------------------------
  // The live window slides: old segments fall off the front of the playlist as
  // new ones appear, so position is tracked by URL, never by index. And the
  // download is paced to buffer depth, not to a fixed clock - decode runs far
  // faster than real time, so an unpaced loop chews through the whole window in
  // seconds and re-downloads the same segments forever.
  TeslaPlayer.prototype.reanchor = function (s) {
    var i = -1;
    for (var k = 0; k < s.segs.length; k++) { if (s.segs[k].url === s.lastUrl) { i = k; break; } }
    // -1 means our last segment has already slid out of the window.
    s.cursor = i >= 0 ? i + 1 : Math.max(0, s.segs.length - 2);
  };

  var sleep = function (ms) { return new Promise(function (r) { setTimeout(r, ms); }); };

  function fetchBufferWithRetry(url, retries) {
    return fetch(url, { cache: 'no-store', priority: 'high' }).then(function (r) {
      if (!r.ok) throw new Error('HTTP ' + r.status);
      return r.arrayBuffer();
    }).catch(function (e) {
      if (retries <= 0) throw e;
      return sleep(800).then(function () {
        return fetchBufferWithRetry(url, retries - 1);
      });
    });
  }

  TeslaPlayer.prototype.pump = function (s, gen) {
    var self = this;
    if (s.pumpRunning) return;
    s.pumpRunning = true;
    (function loop() {
      if (s.stopped || self.gen !== gen) { s.pumpRunning = false; return; }
      if (s.paused) { sleep(200).then(loop); return; }
      if (s.cursor >= s.segs.length) {
        if (s.vod) {
          // A VOD playlist does not grow. Once the downloaded media has played
          // out, the stream is over.
          if (!s.ended && bufferedOf(s) <= 0) {
            s.ended = true;
            self.pause();
            self.emit('ended');
          } else {
            sleep(200).then(loop);
          }
          return;
        }
        fetch(s.base, { cache: 'no-store', priority: 'high' }).then(function (r) {
          return r.ok ? r.text() : Promise.reject(new Error('HTTP ' + r.status));
        }).then(function (t) {
          var p = parsePlaylist(t);
          if (p.segs.length) { s.segs = p.segs; s.target = p.target; s.segDur = p.segs[0].dur; }
          if (s.aBase) {
            fetch(s.aBase, { cache: 'no-store', priority: 'high' }).then(function (ar) {
              return ar.ok ? ar.text() : null;
            }).then(function (at) {
              if (!at) return;
              var ap = parsePlaylist(at);
              if (ap.segs.length) s.aSegs = ap.segs;
            }).catch(function () {});
          }
          self.reanchor(s);
          return sleep(0);
        }).catch(function (e) { return sleep(1500); }).then(function () { loop(); });
        return;
      }
      // Pace by BUFFER DEPTH. One segment per segment-duration means media
      // arrives exactly when it is needed, so the audio ring sits at zero and
      // every hiccup becomes a dropout. Fill well beyond that instead.
      if (bufferedOf(s) > bufferTargetFor(s)) { sleep(200).then(loop); return; }
      var seg = s.segs[s.cursor];
      if (!seg) { sleep(100).then(loop); return; }
      s.cursor++; s.lastUrl = seg.url;
      fetchBufferWithRetry(absolute(seg.url, s.base), 2).then(function (buf) {
        if (s.stopped || self.gen !== gen) return;
        s.fetchErr = '';
        s.segsFetched++;
        if (s.fmp4) {
          self.feedMp4(s, new Uint8Array(buf));
        } else {
          s.tm.push(new Uint8Array(buf));
          // push() only feeds the parser. flush() is what tells mux.js the segment
          // ended, and that is what makes it remux and emit 'data' - without it
          // the transmuxer just buffers and nothing ever comes out.
          s.tm.flush();
        }
        if (s.aSegs && s.aSegs.length && !s.audioFromMux) {
          var aseg = s.aSegs[Math.min(Math.max(0, s.cursor - 1), s.aSegs.length - 1)];
          if (aseg) {
            fetchBufferWithRetry(absolute(aseg.url, s.aBase), 1).then(function (abuf) {
              if (s.stopped || self.gen !== gen) return;
              if (s.aAdts) self.feedAdtsAudio(s, new Uint8Array(abuf));
              else self.feedAudioMp4(s, new Uint8Array(abuf));
            }).catch(function (e) {
              s.aErr = 'audio segment: ' + e.message;
            });
          }
        }
      }).catch(function (e) {
        s.fetchErr = e.message;
      }).then(function () { loop(); });
    })();
  };

  // ---- teardown -----------------------------------------------------------
  // Without this every channel change leaks a VideoDecoder, an AudioDecoder, a
  // paint timer and a pump loop. Flick through a dozen channels and the page
  // is running a dozen pipelines at once.
  TeslaPlayer.prototype.close = function () {
    var s = this.live;
    if (!s) return;
    s.stopped = true;
    this.gen++;                      // orphan every in-flight callback
    this.live = null;
    this.emit('state', this.state());
    try { if (s.vdec && s.vdec.state !== 'closed') s.vdec.close(); } catch (e) {}
    try { if (s.adec && s.adec.state !== 'closed') s.adec.close(); } catch (e) {}
    // The audio graph deliberately SURVIVES a channel switch - it belongs to the
    // player, not the stream. Only the ring's contents are dropped, so the next
    // channel does not play out the tail of this one.
    this.flushAudio();
    try { if (s.tm) s.tm.removeAllListeners(); } catch (e) {}
    try { if (s.mbox) s.mbox.stop(); } catch (e) {}
    try { if (s.ambox) s.ambox.stop(); } catch (e) {}
    try { if (s.paintTimer) clearTimeout(s.paintTimer); } catch (e) {}
    try { if (s.pumpTimer) clearInterval(s.pumpTimer); } catch (e) {}
    try { if (s.statsTimer) clearInterval(s.statsTimer); } catch (e) {}
    try { if (s.rafId) cancelAnimationFrame(s.rafId); } catch (e) {}
    // Release any frames still queued. VideoFrames hold GPU/system memory and
    // an unclosed frame is a leak the GC will not collect.
    for (var i = 0; i < s.fq.length; i++) { try { s.fq[i].frame.close(); } catch (e) {} }
    s.fq.length = 0;
    s.pend.length = 0; s.aPend.length = 0;
  };

  // Tear the persistent audio graph down. Only needed when leaving Drive mode
  // for good - a channel switch must NOT do this, or every switch would rebuild
  // the whole chain and re-register the processor name.
  TeslaPlayer.prototype.destroy = function () {
    this.close();
    var a = this.audio;
    try { if (a.node) { if (a.node.port) a.node.port.onmessage = null; a.node.disconnect(); } } catch (e) {}
    try { if (a.gain) a.gain.disconnect(); } catch (e) {}
    try { if (a.limiter) a.limiter.disconnect(); } catch (e) {}
    try { if (a.analyser) a.analyser.disconnect(); } catch (e) {}
    if (this.actx) { try { this.actx.close(); } catch (e) {} }
    this.actx = null;
    this.audio = { ready: false, pending: null, node: null, push: null, flush: null,
                   setRate: null, setTrim: null, rate: 0, sourceRate: 0, trim: 1,
                   path: '', modErr: '', depth: 0, rms: 0, underruns: 0,
                   gain: null, limiter: null, analyser: null, buf: null };
  };

  TeslaPlayer.prototype.fail = function (msg) {
    if (this.live) { this.live.fatal = msg; this.emit('note', msg); }
    if (this.listeners.fail) this.emit('fail', msg);
  };

  // ---- reporting ----------------------------------------------------------
  TeslaPlayer.prototype.state = function () {
    var s = this.live;
    if (!s) return { stage: 'idle' };
    var st = {
      stage: s.fatal ? 'error' : (s.firstFrameAt ? 'live' : 'starting'),
      channel: s.meta.name || '',
      paused: !!s.paused,
      ended: !!s.ended,
      currentTime: s.vT0 >= 0 ? Math.max(0, (s.startOffset || 0) + ((s.paused && s.pausedAt ? s.pausedAt : Date.now()) - s.vT0) / 1000) : (s.startAt || 0),
      lastDrawnTime: s.lastDrawnTime || 0,
      queueTime: s.fq.length ? s.fq[0].time : 0,
      paintCalls: s.paintCalls || 0,
      paintSkips: s.paintSkips || 0,
      lastWait: s.lastWait || 0,
      duration: s.vod ? s.edgeLen : 0,
      url: s.url,
      master: !!s.master,
      codec: s.codec, width: s.width, height: s.height,
      srcRate: s.srcRate, srcCh: s.srcCh || 2, fps: s.frameIv ? (1000 / s.frameIv) : 0,
      drawn: s.drawn, drops: s.drops, segs: s.segsFetched,
      audioPath: this.audio.path, modErr: this.audio.modErr,
      muted: this.muted,
      ctxState: this.actx ? this.actx.state : 'none',
      aFrames: s.aFrames, aSeconds: s.aSeconds, aUnder: this.audio.underruns,
      aQueue: this.audio.depth, aRms: this.audio.rms,
      // aDrift is the sound's position against the picture: positive means the
      // audio is ahead, negative behind, zero in sync. aTrim is the resample
      // correction being applied to hold it there.
      aDrift: this.audio.depth ? (AUDIO_LEAD_S - this.audio.depth) : 0,
      aTrim: s.aTrim || 1,
      outRms: this.outRms(),
      buffered: bufferedOf(s),
      bufferTarget: bufferTargetFor(s),
      fatal: s.fatal, fetchErr: s.fetchErr, aErr: s.aErr || '',
      firstFrameMs: s.firstFrameAt ? (s.firstFrameAt - s.t0) : 0
    };
    // The paint interval is the number that says whether the picture is smooth.
    // 40ms for a 25fps source is perfect; 50ms means judder.
    if (s.gaps.length > 4) {
      var g = s.gaps.slice().sort(function (a, b) { return a - b; });
      st.medGap = Math.round(g[Math.floor(g.length / 2)]);
      st.worstGap = Math.round(g[Math.floor(g.length * 0.95)]);
      st.spread = Math.round(g[Math.floor(g.length * 0.9)] - g[Math.floor(g.length / 2)]);
    }
    st.canvW = this.canvas.width; st.canvH = this.canvas.height;
    return st;
  };

  // Level actually leaving the graph, measured after the gain and the limiter.
  // Reading it before the gain would say nothing about audibility.
  TeslaPlayer.prototype.outRms = function () {
    var a = this.audio;
    if (!a.analyser || !a.buf) return 0;
    a.analyser.getFloatTimeDomainData(a.buf);
    var sum = 0;
    for (var i = 0; i < a.buf.length; i++) sum += a.buf[i] * a.buf[i];
    return Math.sqrt(sum / a.buf.length);
  };

  global.TeslaPlayer = TeslaPlayer;
  global.TeslaEngine = {
    missingLibs: missingLibs,
    RING_WORKLET: RING_WORKLET
  };
})(window);

(() => {
  'use strict';

  const APIS = [
    'https://pipedapi.dedyn.io',
    'https://api.piped.private.coffee',
    'https://pipedapi.ducks.party'
  ];
  const PIPED_FALLBACK = [
    'https://pipedapi.kavin.rocks',
    'https://pipedapi.tokhmi.xyz',
    'https://pipedapi.moomoo.me',
    'https://pipedapi.syncpundit.io',
    'https://api-piped.mha.fi',
    'https://piped-api.garudalinux.org',
    'https://pipedapi.rivo.lol',
    'https://pipedapi.leptons.xyz',
    'https://piped-api.lunar.icu',
    'https://ytapi.dc09.ru',
    'https://pipedapi.colinslegacy.com',
    'https://yapi.vyper.me',
    'https://api.looleh.xyz',
    'https://piped-api.cfe.re',
    'https://pipedapi.r4fo.com',
    'https://pipedapi.darkness.services',
    'https://pipedapi-libre.kavin.rocks',
    'https://pa.mint.lgbt',
    'https://pa.il.ax',
    'https://piped-api.privacy.com.de',
    'https://api.piped.projectsegfau.lt',
    'https://pipedapi.in.projectsegfau.lt',
    'https://pipedapi.us.projectsegfau.lt',
    'https://watchapi.whatever.social',
    'https://api.piped.privacydev.net',
    'https://pipedapi.palveluntarjoaja.eu',
    'https://pipedapi.smnz.de',
    'https://pipedapi.adminforge.de',
    'https://pipedapi.qdi.fi',
    'https://piped-api.hostux.net',
    'https://pdapi.vern.cc',
    'https://pipedapi.reallyaweso.me',
    'https://pipedapi.frontendfriendly.xyz',
    'https://api.piped.yt',
    'https://pipedapi.astartes.nl',
    'https://pipedapi.osphost.fi',
    'https://pipedapi.simpleprivacy.fr',
    'https://pipedapi.drgns.space',
    'https://piapi.ggtyler.dev',
    'https://api.watch.pluto.lat',
    'https://piped-backend.seitan-ayoub.lol',
    'https://pipedapi.owo.si',
    'https://api.piped.minionflo.net',
    'https://pipedapi.nezumi.party',
    'https://pipedapi.ngn.tf',
    'https://pipedapi.coldforge.xyz',
    'https://piped-api.codespace.cz',
    'https://pipedapi.phoenixthrush.com',
    'https://schaunapi.ehwurscht.at',
    'https://pipedapi.nosebs.ru'
  ];
  const INVIDIOUS_FALLBACK = [
    'https://invidious.flokinet.to',
    'https://invidious.f5.si',
    'https://inv.nadeko.net',
    'https://invidious.tiekoetter.com',
    'https://invidious.nerdvpn.de',
    'https://invidious.reallyaweso.me',
    'https://invidious.private.coffee',
    'https://yt.chocolatemoo53.com',
    'https://invidious.perennialte.ch',
    'https://iv.datura.network',
    'https://invidious.protokolla.fi',
    'https://iv.ggtyler.dev'
  ];
  const INSTANCE_LIST_URL = 'https://api.invidious.io/instances.json?sort_by=health';
  const API_TIMEOUT = 9000;
  const DEFAULT_YATTEE_URL = 'https://yattee.vpmbd45g3cfj.opentunnel.xyz';
  const DEFAULT_YATTEE_USER = 'xix';

  function maxDefinition() {
    try {
      return localStorage.getItem('youtube:allow-1080') === '1' ? 1080 : 720;
    } catch (e) {
      return 720;
    }
  }

  function yatteeConfig() {
    try {
      const saved = JSON.parse(localStorage.getItem('youtube:yattee') || 'null');
      if (saved && typeof saved === 'object') {
        return {
          url: typeof saved.url === 'string' ? saved.url : DEFAULT_YATTEE_URL,
          user: typeof saved.user === 'string' ? saved.user : DEFAULT_YATTEE_USER,
          password: typeof saved.password === 'string' ? saved.password : ''
        };
      }
    } catch (e) {}
    return { url: DEFAULT_YATTEE_URL, user: DEFAULT_YATTEE_USER, password: '' };
  }

  function saveYatteeConfig(config) {
    try {
      localStorage.setItem('youtube:yattee', JSON.stringify(config));
      return true;
    } catch (e) {
      return false;
    }
  }

  function yatteeEnabled() {
    const config = yatteeConfig();
    return Boolean(config.url.trim() && config.password);
  }

  function yatteeOnly() {
    try {
      return localStorage.getItem('youtube:yattee-only') === '1';
    } catch (e) {
      return false;
    }
  }

  function clearWatchCache() {
    try {
      const keys = [];
      for (let i = 0; i < localStorage.length; i++) {
        const key = localStorage.key(i);
        if (key && key.startsWith('youtube:watch:')) keys.push(key);
      }
      for (const key of keys) localStorage.removeItem(key);
    } catch (e) {}
  }

  function sourceHost(value) {
    try {
      return new URL(value).host;
    } catch (e) {
      return String(value || '').replace(/^https?:\/\//, '').split('/')[0];
    }
  }

  function streamSourceLabel(video) {
    if (!video) return 'Unknown source';
    if ((!video.streamSource || video.streamSource === 'public') && lastSource) {
      video.streamSource = lastSource.type;
      video.streamOrigin = sourceHost(lastSource.base);
    }
    const origin = video.streamOrigin || '';
    if (video.streamSource === 'yattee') {
      return origin ? `Yattee · ${origin}` : 'Yattee';
    }
    if (video.streamSource === 'invidious') {
      return origin ? `Invidious · ${origin}` : 'Invidious';
    }
    if (video.streamSource === 'piped') {
      return origin ? `Piped · ${origin}` : 'Piped';
    }
    if (origin) {
      return `Piped · ${origin}`;
    }
    return 'Piped';
  }

  function basicAuthHeader(user, password) {
    try {
      const bytes = new TextEncoder().encode(`${user}:${password}`);
      let binary = '';
      for (const byte of bytes) binary += String.fromCharCode(byte);
      return `Basic ${btoa(binary)}`;
    } catch (e) {
      return '';
    }
  }
  const ID_RE = /^[A-Za-z0-9_-]{11}$/;
  const REGION = (() => {
    try {
      return new Intl.Locale(navigator.language).region || 'US';
    } catch (e) {
      return 'US';
    }
  })();
  const CHIPS = [
    ['All', '?'],
    ['Music', '?q=music'],
    ['Live', '?q=live'],
    ['News', '?q=news'],
    ['Podcasts', '?q=podcasts'],
    ['Movies', '?q=movies'],
    ['Technology', '?q=technology'],
    ['Cooking', '?q=cooking']
  ];
  const listCache = new Map();
  const publicFallbacks = new Map();
  const fallbackAttempts = new WeakSet();
  const $ = (selector, root = document) => root.querySelector(selector);

  const view = $('#view');
  const searchForm = $('#searchForm');
  const searchInput = $('#searchInput');
  const searchSuggestions = $('#searchSuggestions');
  const menuBtn = $('#menuBtn');
  const themeBtn = $('#themeBtn');
  const themeColor = $('#themeColor');
  const scrim = $('#scrim');

  let routeSeq = 0;
  let routeAbort = null;
  let currentHls = null;
  let currentVideo = null;
  let currentEngine = null;
  let currentEngineSyncTimer = 0;
  let currentEnginePlayer = null;
  let currentEngineSeekHandler = null;
  let hlsPromise = null;
  let instanceCache = { fetchedAt: 0, invidious: [] };
  let lastSource = null;
  try {
    const storedSource = JSON.parse(localStorage.getItem('youtube:last-source') || 'null');
    if (storedSource && storedSource.base && storedSource.type) lastSource = storedSource;
  } catch (e) {}
  const videoCache = new Map();

  const esc = (value) =>
    String(value ?? '').replace(/[&<>"']/g, (ch) => ({
      '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'
    })[ch]);

  const icon = (name, cls = '') => `<svg class="icon ${cls}"><use href="#i-${name}"/></svg>`;

  const compactNumber = new Intl.NumberFormat('en', {
    notation: 'compact',
    maximumFractionDigits: 1
  });
  const relativeTime = new Intl.RelativeTimeFormat('en', { numeric: 'auto' });

  function fmtCount(value) {
    const number = Number(value);
    if (!Number.isFinite(number) || number < 0) return '';
    return compactNumber.format(number);
  }

  function fmtViews(value) {
    const count = fmtCount(value);
    return count ? `${count} views` : '';
  }

  function fmtDuration(value) {
    const total = Math.max(0, Math.floor(Number(value) || 0));
    const hours = Math.floor(total / 3600);
    const minutes = Math.floor((total % 3600) / 60);
    const seconds = total % 60;
    if (hours) {
      return `${hours}:${String(minutes).padStart(2, '0')}:${String(seconds).padStart(2, '0')}`;
    }
    return `${minutes}:${String(seconds).padStart(2, '0')}`;
  }

  function fmtQuality(height) {
    const lines = Number(height);
    return `${lines > 0 ? lines : maxDefinition()}p`;
  }

  function updateQualityBadge(height, fps) {
    const label = $('#qualityText');
    if (!label || !Number(height)) return;
    label.textContent = fmtQuality(height);
  }

  function timeAgo(timestamp) {
    const time = Number(timestamp);
    if (!Number.isFinite(time) || time <= 0) return '';
    const diff = time - Date.now();
    const units = [
      ['year', 31536000000],
      ['month', 2592000000],
      ['week', 604800000],
      ['day', 86400000],
      ['hour', 3600000],
      ['minute', 60000]
    ];
    for (const [unit, ms] of units) {
      if (Math.abs(diff) >= ms) return relativeTime.format(Math.round(diff / ms), unit);
    }
    return 'just now';
  }

  function extractVideoId(input) {
    const text = String(input ?? '').trim();
    if (ID_RE.test(text)) return text;
    const match =
      text.match(/[?&]v=([A-Za-z0-9_-]{11})(?:[&#]|$)/) ||
      text.match(/(?:youtu\.be\/|\/(?:shorts|embed|live)\/)([A-Za-z0-9_-]{11})(?=[?&#/]|$)/);
    return match ? match[1] : '';
  }

  function parseStart(value) {
    if (!value) return 0;
    if (/^\d+$/.test(value)) return Number(value);
    const colon = value.match(/^(\d+):(\d{1,2})(?::(\d{1,2}))?$/);
    if (colon) {
      return colon[3]
        ? Number(colon[1]) * 3600 + Number(colon[2]) * 60 + Number(colon[3])
        : Number(colon[1]) * 60 + Number(colon[2]);
    }
    const units = value.match(/^(?:(\d+)h)?(?:(\d+)m)?(?:(\d+)s)?$/i);
    if (units) {
      return Number(units[1] || 0) * 3600 + Number(units[2] || 0) * 60 + Number(units[3] || 0);
    }
    return 0;
  }

  function plainText(html) {
    const holder = document.createElement('textarea');
    holder.innerHTML = String(html || '').replace(/<br\s*\/?>/gi, '\n');
    return holder.value
      .replace(/<[^>]*>/g, '')
      .replace(/\u200b/g, '')
      .replace(/\u00a0/g, ' ')
      .replace(/[ \t]+\n/g, '\n')
      .replace(/\n{3,}/g, '\n\n')
      .trim()
      .slice(0, 8000);
  }

  function initials(name) {
    return Array.from(String(name || '?').trim())[0] || '?';
  }

  function channelColor(name) {
    const colors = ['#7b1fa2', '#c2185b', '#d32f2f', '#e64a19', '#5d4037', '#455a64', '#00796b', '#388e3c', '#1e88e5', '#5e35b1', '#00838f', '#6d4c41'];
    let hash = 0;
    for (const ch of String(name || '')) hash = (hash * 31 + ch.charCodeAt(0)) | 0;
    return colors[Math.abs(hash) % colors.length];
  }

  function directImageURL(url) {
    try {
      const parsed = new URL(url);
      const host = parsed.searchParams.get('host');
      if (host && /^[a-z0-9.-]+$/i.test(host)) {
        return `${parsed.protocol}//${host}${parsed.pathname}`;
      }
    } catch (e) {}
    return url;
  }

  function avatarHTML(name, url = '') {
    const original = String(url || '').trim();
    const src = directImageURL(original);
    const fallback = src !== original ? original : '';
    const image = /^https?:\/\//i.test(src)
      ? `<img class="avatar-img" src="${esc(src)}"${fallback ? ` data-fallback="${esc(fallback)}"` : ''} alt="" loading="lazy" decoding="async" referrerpolicy="no-referrer">`
      : '';
    return `<span class="avatar" style="--av:${channelColor(name)}" aria-hidden="true">${esc(initials(name))}${image}</span>`;
  }

  function channelURL(video) {
    const raw = String(video.uploaderUrl || '');
    const id = raw.match(/\/(?:channel|c|user)\/([A-Za-z0-9_-]+)/);
    if (id) return `?channel=${id[1]}`;
    const handle = raw.match(/(?:^|\/)@([A-Za-z0-9._-]+)/);
    if (handle) return `?channel=@${handle[1]}`;
    return `?q=${encodeURIComponent(video.channel)}`;
  }

  function absoluteURL(url, base) {
    const raw = String(url || '');
    if (!raw) return '';
    if (/^https?:\/\//i.test(raw)) return raw;
    try {
      return new URL(raw, base).href;
    } catch (e) {
      return raw;
    }
  }

  function parseQualityLabel(label) {
    const match = String(label || '').match(/(\d{3,4})p/);
    return match ? Number(match[1]) : 0;
  }

  function formatHeight(format) {
    const labelled = parseQualityLabel(format && format.qualityLabel);
    if (labelled) return labelled;
    const height = Number(format && format.height);
    if (height > 0) return height;
    const known = {
      18: 360, 22: 720, 37: 1080, 43: 360, 44: 480,
      45: 720, 46: 1080, 59: 480, 78: 480, 85: 720, 93: 1080
    };
    return known[String(format && format.itag)] || 0;
  }

  async function fetchInvidiousInstance(base, id, signal, timeout) {
    const controller = new AbortController();
    const abort = () => controller.abort();
    if (signal) signal.addEventListener('abort', abort);
    const timer = setTimeout(() => controller.abort(), timeout);
    try {
      const response = await fetch(`${base}/api/v1/videos/${encodeURIComponent(id)}?local=true`, {
        signal: controller.signal,
        headers: { Accept: 'application/json' },
        priority: 'high'
      });
      if (!response.ok) throw new Error('Unexpected response');
      const data = await response.json();
      const formats = (data.formatStreams || []).filter((format) =>
        format && format.url &&
        (format.container === 'mp4' ||
          String(format.mimeType || '').startsWith('video/') ||
          format.itag === '18' || format.itag === '22')
      );
      const limit = maxDefinition();
      const capped = formats.filter((format) => {
        const height = formatHeight(format);
        return height > 0 && height <= limit;
      });
      if (!capped.length && !data.hlsUrl) throw new Error('No playable stream');
      capped.sort((a, b) => formatHeight(b) - formatHeight(a));
      return { base, data, stream: capped[0] || null };
    } finally {
      clearTimeout(timer);
      if (signal) signal.removeEventListener('abort', abort);
    }
  }

  async function fetchInvidiousCandidate(base, id, signal) {
    const entry = await fetchInvidiousInstance(base, id, signal, 8000);
    return normalizeInvidious(entry, id);
  }

  async function fetchYatteeStream(id, signal) {
    const config = yatteeConfig();
    if (!config.url || !config.password) return null;
    const base = config.url.replace(/\/+$/, '');
    const controller = new AbortController();
    const abort = () => controller.abort();
    if (signal) signal.addEventListener('abort', abort);
    const timer = setTimeout(() => controller.abort(), 6000);
    try {
      const response = await fetch(
        `${base}/api/v1/videos/${encodeURIComponent(id)}?proxy=true&proxy_mode=relay`,
        {
          signal: controller.signal,
          cache: 'no-store',
          priority: 'high',
          headers: {
            Accept: 'application/json',
            Authorization: basicAuthHeader(config.user, config.password)
          }
        }
      );
      if (!response.ok) return null;
      const data = await response.json();
      const limit = maxDefinition();
      const formatList = Array.isArray(data.formatStreams) ? data.formatStreams : [];
      const hlsFormat = formatList.find((format) =>
        format && format.url &&
        (format.container === 'hls' ||
          /mpegurl/i.test(String(format.mimeType || '')) ||
          /\.m3u8(?:\?|$)/i.test(String(format.url)))
      );
      if (!data.hlsUrl && hlsFormat) data.hlsUrl = hlsFormat.url;
      const formats = formatList.filter((format) =>
        format && format.url &&
        (format.container === 'mp4' ||
          String(format.mimeType || '').startsWith('video/') ||
          format.itag === '18' || format.itag === '22')
      );
      const capped = formats.filter((format) => {
        const height = formatHeight(format);
        return height > 0 && height <= limit;
      });
      capped.sort((a, b) => formatHeight(b) - formatHeight(a));
      const stream = capped[0] || null;
      const hls = data.hlsUrl ? absoluteURL(data.hlsUrl, base) : '';
      if (!stream && !hls) return null;
      return normalizeInvidious({ base, data, stream }, id);
    } catch (e) {
      if (signal && signal.aborted) throw new DOMException('Aborted', 'AbortError');
      return null;
    } finally {
      clearTimeout(timer);
      if (signal) signal.removeEventListener('abort', abort);
    }
  }

  function normalizeInvidious(entry, id) {
    const { base, data, stream } = entry;
    const avatar = (data.authorThumbnails || []).slice(-1)[0];
    const related = (data.recommendedVideos || [])
      .map((item) => {
        const thumb = (item.authorThumbnails || []).slice(-1)[0];
        return {
          id: item.videoId,
          title: item.title || 'Untitled',
          channel: item.author || 'Unknown',
          uploaderUrl: item.authorUrl || '',
          avatar: thumb ? absoluteURL(thumb.url, base) : '',
          views: Number(item.viewCount ?? -1),
          duration: Number(item.lengthSeconds ?? 0),
          live: item.liveNow === true,
          when: item.publishedText || '',
          description: ''
        };
      })
      .filter((item) => item.id && item.id !== id)
      .slice(0, 20);
    return {
      id,
      title: data.title || 'Untitled',
      channel: data.author || 'Unknown',
      uploaderUrl: data.authorUrl || '',
      avatar: avatar ? absoluteURL(avatar.url, base) : '',
      subscribers: -1,
      views: Number(data.viewCount ?? -1),
      likes: Number(data.likeCount ?? -1),
      live: data.liveNow === true,
      duration: Number(data.lengthSeconds || 0),
      hls: data.hlsUrl ? absoluteURL(data.hlsUrl, base) : '',
      source: stream ? absoluteURL(stream.url, base) : '',
      quality: stream ? { height: parseQualityLabel(stream.qualityLabel), fps: 0 } : null,
      directQuality: stream ? { height: parseQualityLabel(stream.qualityLabel), fps: 0 } : null,
      originalAudio: null,
      description: plainText(data.description || ''),
      when: data.publishedText || '',
      related
    };
  }

  function thumbURL(id) {
    return `https://i.ytimg.com/vi/${id}/hqdefault.jpg`;
  }

  function thumbHTML(video, className = '') {
    const badge = video.live
      ? '<span class="badge live">LIVE</span>'
      : video.duration > 0
        ? `<span class="badge">${fmtDuration(video.duration)}</span>`
        : '';
    return `<div class="thumb ${className}">
      <img src="${thumbURL(video.id)}" alt="" loading="lazy" decoding="async" referrerpolicy="no-referrer"
        onerror="this.onerror=null;this.src='https://i.ytimg.com/vi/${video.id}/mqdefault.jpg'">
      ${badge}
    </div>`;
  }

  function itemMeta(video) {
    if (video.live) {
      return video.views >= 0 ? `${fmtCount(video.views)} watching` : 'Live now';
    }
    return [fmtViews(video.views), video.when].filter(Boolean).join(' • ');
  }

  function normalizeItem(item) {
    if (!item || typeof item !== 'object') return null;
    const id = extractVideoId(item.url || item.videoId || '');
    if (!id) return null;
    const uploadedAt = Number(item.uploaded);
    const scheduled = Number.isFinite(uploadedAt) && uploadedAt > Date.now() + 60000;
    const live = !scheduled && (item.duration === -1 || item.livestream === true ||
      item.liveNow === true || item.isLive === true);
    return {
      id,
      title: item.title || 'Untitled',
      channel: item.uploaderName || item.uploader || 'Unknown',
      views: Number(item.views ?? -1),
      duration: Number(item.duration ?? 0),
      live,
      when: item.uploadedDate || (Number(item.uploaded) > 0 ? timeAgo(item.uploaded) : ''),
      description: plainText(item.shortDescription || ''),
      uploaderUrl: item.uploaderUrl || '',
      avatar: item.uploaderAvatar || ''
    };
  }

  function normalizeItems(payload) {
    const list = Array.isArray(payload)
      ? payload
      : payload && Array.isArray(payload.items)
        ? payload.items
        : [];
    return list
      .filter((item) => item && item.type !== 'channel' && item.type !== 'playlist')
      .map(normalizeItem)
      .filter(Boolean);
  }

  function streamHeight(stream) {
    const height = Number(stream && stream.height) || 0;
    if (height > 0) return height;
    const match = String((stream && stream.quality) || '').match(/(\d{3,4})p/);
    return match ? Number(match[1]) : 0;
  }

  function progressiveStreams(videoStreams) {
    return (Array.isArray(videoStreams) ? videoStreams : [])
      .filter((stream) => {
        if (!stream || !stream.url || stream.videoOnly === true) return false;
        const mime = String(stream.mimeType || '').toLowerCase();
        return !mime.includes('mpegurl') && (!mime || mime.startsWith('video/'));
      })
      .sort((a, b) => streamHeight(b) - streamHeight(a) || Number(b.bitrate) - Number(a.bitrate));
  }

  function normalizeStream(data, id) {
    const uploaded = Number(data.uploaded) > 0
      ? Number(data.uploaded)
      : Date.parse(data.uploadDate || '');
    const related = Array.isArray(data.relatedStreams)
      ? data.relatedStreams
          .map(normalizeItem)
          .filter((item) => item && item.id !== id)
          .slice(0, 20)
      : [];
    const audioStreams = Array.isArray(data.audioStreams) ? data.audioStreams : [];
    const originalAudio = audioStreams.find(
      (track) => String(track.audioTrackType || '').toUpperCase() === 'ORIGINAL'
    );
    const videoStreams = Array.isArray(data.videoStreams) ? data.videoStreams : [];
    const limit = maxDefinition();
    const progressive = progressiveStreams(videoStreams).find((stream) => {
      const height = streamHeight(stream);
      return height > 0 && height <= limit;
    });
    const bestVideo = videoStreams
      .filter((stream) => {
        const height = streamHeight(stream);
        return height > 0 && height <= limit;
      })
      .sort((a, b) => streamHeight(b) - streamHeight(a) || Number(b.fps) - Number(a.fps))[0];
    const qualityStream = data.hls ? bestVideo : progressive || bestVideo;
    return {
      id,
      title: data.title || 'Untitled',
      channel: data.uploader || 'Unknown',
      uploaderUrl: data.uploaderUrl || '',
      avatar: data.uploaderAvatar || '',
      subscribers: Number(data.uploaderSubscriberCount ?? -1),
      views: Number(data.views ?? -1),
      likes: Number(data.likes ?? -1),
      live: data.livestream === true,
      duration: Number(data.duration || 0),
      hls: data.hls || '',
      source: progressive ? progressive.url : '',
      quality: qualityStream
        ? { height: streamHeight(qualityStream), fps: Number(qualityStream.fps) || 0 }
        : null,
      directQuality: progressive
        ? { height: streamHeight(progressive), fps: Number(progressive.fps) || 0 }
        : null,
      originalAudio: originalAudio
        ? {
            name: originalAudio.audioTrackName || '',
            lang: originalAudio.audioTrackLocale || ''
          }
        : null,
      description: plainText(data.description || ''),
      when: uploaded ? timeAgo(uploaded) : '',
      related
    };
  }

  function hasPlayableStream(data) {
    if (!data || !data.title) return false;
    if (data.hls) return true;
    const limit = maxDefinition();
    return progressiveStreams(data.videoStreams).some((stream) => {
      const height = streamHeight(stream);
      return height > 0 && height <= limit;
    });
  }

  function cardHTML(video) {
    videoCache.set(video.id, video);
    return `<a class="card" href="?v=${video.id}" data-nav title="${esc(video.title)}">
      ${thumbHTML(video)}
      <div class="card-body">
            ${avatarHTML(video.channel, video.avatar)}
        <div class="card-text">
          <h3 class="card-title">${esc(video.title)}</h3>
          <div class="card-channel">${esc(video.channel)}</div>
          <div class="card-meta">${esc(itemMeta(video))}</div>
        </div>
      </div>
    </a>`;
  }

  function resultHTML(video) {
    videoCache.set(video.id, video);
    return `<a class="result" href="?v=${video.id}" data-nav>
      ${thumbHTML(video)}
      <div class="result-info">
        <h3 class="result-title">${esc(video.title)}</h3>
        <div class="result-meta">${esc(itemMeta(video))}</div>
        <div class="result-channel">${esc(video.channel)}</div>
        ${video.description ? `<div class="result-desc">${esc(video.description)}</div>` : ''}
      </div>
    </a>`;
  }

  function compactHTML(video) {
    videoCache.set(video.id, video);
    return `<a class="compact" href="?v=${video.id}" data-nav title="${esc(video.title)}">
      ${thumbHTML(video)}
      <div class="compact-info">
        <h3 class="compact-title">${esc(video.title)}</h3>
        <div class="compact-channel">${esc(video.channel)}</div>
        <div class="compact-meta">${esc(itemMeta(video))}</div>
      </div>
    </a>`;
  }

  function chipsHTML() {
    return `<div class="chipbar">${CHIPS.map(([label, href], index) =>
      `<a class="chip${index === 0 ? ' active' : ''}" href="${href}" data-nav>${label}</a>`
    ).join('')}</div>`;
  }

  function skeletonCard() {
    return `<div class="skeleton-card" aria-hidden="true">
      <div class="sk sk-thumb"></div>
      <div class="sk-body">
        <div class="sk sk-avatar"></div>
        <div>
          <div class="sk sk-line title"></div>
          <div class="sk sk-line short"></div>
          <div class="sk sk-line short"></div>
        </div>
      </div>
    </div>`;
  }

  function skeletonGrid(count = 12) {
    return `<div class="grid" aria-hidden="true">${Array.from({ length: count }, skeletonCard).join('')}</div>`;
  }

  function skeletonResults(count = 8) {
    return `<div aria-hidden="true">${Array.from({ length: count }, () => `
      <div class="skeleton-result">
        <div class="sk sk-thumb"></div>
        <div>
          <div class="sk sk-line title"></div>
          <div class="sk sk-line short"></div>
          <div class="sk sk-line" style="width:76%;margin-top:12px"></div>
          <div class="sk sk-line short"></div>
        </div>
      </div>`).join('')}</div>`;
  }

  function skeletonCompactList(count = 8) {
    return Array.from({ length: count }, () => `
      <div class="compact" aria-hidden="true">
        <div class="sk sk-thumb"></div>
        <div>
          <div class="sk sk-line title"></div>
          <div class="sk sk-line short"></div>
        </div>
      </div>`).join('');
  }

  function stateHTML(title, detail, actions = '') {
    return `<div class="state">
      ${icon('alert')}
      <h2>${esc(title)}</h2>
      <p>${esc(detail)}</p>
      ${actions ? `<div class="status-actions">${actions}</div>` : ''}
    </div>`;
  }

  function errorStateHTML(title, detail, retry = true) {
    const actions = retry
      ? `<button class="btn" type="button" data-retry>${icon('refresh')}<span>Try again</span></button>`
      : '';
    return stateHTML(title, detail, actions);
  }

  async function apiFetch(base, path, signal) {
    const controller = new AbortController();
    const abort = () => controller.abort();
    if (signal) {
      if (signal.aborted) throw new DOMException('Aborted', 'AbortError');
      signal.addEventListener('abort', abort, { once: true });
    }
    const timer = setTimeout(() => controller.abort(), API_TIMEOUT);
    try {
      const response = await fetch(`${base}${path}`, {
        signal: controller.signal,
        headers: { Accept: 'application/json' },
        cache: 'no-store',
        priority: 'high'
      });
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      const data = await response.json();
      if (data && data.error) throw new Error('API error');
      return data;
    } finally {
      clearTimeout(timer);
      if (signal) signal.removeEventListener('abort', abort);
    }
  }

  const sleepMs = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

  function yatteeApiBase() {
    const config = yatteeConfig();
    if (!config.url || !config.password) return '';
    return config.url.replace(/\/+$/, '');
  }

  async function yatteeApiFetch(path, signal, timeout = 8000) {
    const base = yatteeApiBase();
    if (!base) throw new Error('Yattee is not configured');
    const config = yatteeConfig();
    const controller = new AbortController();
    const abort = () => controller.abort();
    if (signal) signal.addEventListener('abort', abort, { once: true });
    const timer = setTimeout(() => controller.abort(), timeout);
    try {
      const response = await fetch(`${base}${path}`, {
        signal: controller.signal,
        cache: 'no-store',
        priority: 'high',
        headers: {
          Accept: 'application/json',
          Authorization: basicAuthHeader(config.user, config.password)
        }
      });
      if (!response.ok) throw new Error('Yattee HTTP ' + response.status);
      return response.json();
    } finally {
      clearTimeout(timer);
      if (signal) signal.removeEventListener('abort', abort);
    }
  }

  function yatteeListPath(path) {
    let parsed;
    try {
      parsed = new URL(path, 'https://local.invalid');
    } catch (e) {
      return '';
    }
    if (parsed.pathname === '/trending') {
      const region = parsed.searchParams.get('region') || REGION;
      return `/api/v1/trending?region=${encodeURIComponent(region)}&type=Default`;
    }
    if (parsed.pathname === '/search') {
      const query = parsed.searchParams.get('q') || '';
      if (!query) return '';
      const type = parsed.searchParams.get('filter') === 'channels' ? 'channel' : 'video';
      return `/api/v1/search?q=${encodeURIComponent(query)}&type=${type}`;
    }
    return '';
  }

  function yatteeListToPiped(data, channelList) {
    const list = Array.isArray(data) ? data : (data && Array.isArray(data.items) ? data.items : []);
    const converted = [];
    for (const item of list) {
      if (!item || typeof item !== 'object') continue;
      if (channelList) {
        if (item.type !== 'channel' || !item.authorId) continue;
        const thumb = (item.authorThumbnails || []).slice(-1)[0];
        converted.push({
          url: `/channel/${item.authorId}`,
          type: 'channel',
          name: item.author || 'Channel',
          thumbnail: thumb ? thumb.url : '',
          subscribers: Number(item.subCount ?? -1),
          verified: item.authorVerified === true
        });
        continue;
      }
      if (item.type === 'channel' || !item.videoId) continue;
      const thumb = (item.authorThumbnails || []).slice(-1)[0];
      const live = item.liveNow === true;
      converted.push({
        url: `/watch?v=${item.videoId}`,
        type: 'stream',
        title: item.title || 'Untitled',
        uploaderName: item.author || 'Unknown',
        uploaderUrl: item.authorId ? `/channel/${item.authorId}` : '',
        uploaderAvatar: thumb ? thumb.url : '',
        duration: live ? -1 : Number(item.lengthSeconds || 0),
        livestream: live,
        views: Number(item.viewCount ?? -1),
        uploadedDate: item.publishedText || '',
        shortDescription: item.description || ''
      });
    }
    return converted;
  }

  function apiRace(path, valid, signal) {
    const attempts = APIS.map(async (base) => {
      const data = await apiFetch(base, path, signal);
      if (valid && !valid(data)) throw new Error('Unexpected response');
      return data;
    });
    const publicPromise = Promise.any(attempts);
    const channelList = path.includes('filter=channels');
    const yatteePath = yatteeEnabled() ? yatteeListPath(path) : '';
    if (!yatteePath) return publicPromise;

    return new Promise((resolve, reject) => {
      let done = false;
      let primaryFailed = false;
      let primaryError = null;
      let fallbackStarted = false;
      let timer = 0;
      const finish = (data) => {
        if (done) return;
        done = true;
        clearTimeout(timer);
        resolve(data);
      };
      const fallback = () => {
        if (done || fallbackStarted) return;
        fallbackStarted = true;
        yatteeApiFetch(yatteePath, signal).then((data) => {
          const converted = yatteeListToPiped(data, channelList);
          if (valid && !valid(converted)) throw new Error('Unexpected Yattee response');
          finish(converted);
        }).catch((e) => {
          if (primaryFailed && !done) {
            done = true;
            clearTimeout(timer);
            reject(primaryError || e);
          }
        });
      };
      timer = setTimeout(fallback, 850);
      publicPromise.then(finish, (error) => {
        primaryFailed = true;
        primaryError = error;
        clearTimeout(timer);
        fallback();
      });
    });
  }

  async function fetchPipedCandidate(base, id, signal) {
    const data = await apiFetch(base, `/streams/${encodeURIComponent(id)}`, signal);
    if (!hasPlayableStream(data)) throw new Error('No playable stream');
    return normalizeStream(data, id);
  }

  function refreshInstanceCache() {
    const now = Date.now();
    if (instanceCache.loading || now - instanceCache.fetchedAt < 1800000) return;
    instanceCache.loading = true;
    fetch(INSTANCE_LIST_URL, { headers: { Accept: 'application/json' } })
      .then((response) => (response.ok ? response.json() : null))
      .then((list) => {
        if (!Array.isArray(list)) return;
        instanceCache = {
          fetchedAt: Date.now(),
          invidious: list
            .filter((entry) =>
              Array.isArray(entry) && entry[1] &&
              entry[1].api === true && entry[1].type === 'https'
            )
            .map((entry) => `https://${entry[0]}`)
        };
      })
      .catch(() => {})
      .finally(() => {
        instanceCache.loading = false;
      });
  }

  function getStreamCandidates() {
    refreshInstanceCache();
    const candidates = [];
    const seen = new Set();
    const push = (type, base) => {
      const key = `${type}|${base}`;
      if (seen.has(key)) return;
      seen.add(key);
      candidates.push({ type, base });
    };
    for (const base of APIS) push('piped', base);
    for (const base of INVIDIOUS_FALLBACK) push('invidious', base);
    for (const base of PIPED_FALLBACK) push('piped', base);
    for (const base of instanceCache.invidious || []) push('invidious', base);
    if (lastSource) {
      candidates.sort((a, b) => {
        const aCached = a.type === lastSource.type && a.base === lastSource.base ? 0 : 1;
        const bCached = b.type === lastSource.type && b.base === lastSource.base ? 0 : 1;
        if (aCached !== bCached) return aCached - bCached;
        const aPrimary = a.type === 'piped' && APIS.includes(a.base) ? 0 : 1;
        const bPrimary = b.type === 'piped' && APIS.includes(b.base) ? 0 : 1;
        return aPrimary - bPrimary;
      });
    }
    return candidates;
  }

  function loadPublicStream(id, signal) {
    const candidates = getStreamCandidates();
    if (signal && signal.aborted) throw new DOMException('Aborted', 'AbortError');
    return new Promise((resolve, reject) => {
      let finished = false;
      let settled = 0;
      let best = null;
      let graceTimer = 0;
      const controllers = [];
      const cleanup = () => {
        clearTimeout(graceTimer);
        if (signal) signal.removeEventListener('abort', onAbort);
        for (const controller of controllers) controller.abort();
      };
      const fail = () => {
        if (finished) return;
        finished = true;
        cleanup();
        reject(new Error('No playable stream'));
      };
      const onAbort = () => {
        if (finished) return;
        finished = true;
        clearTimeout(graceTimer);
        for (const controller of controllers) controller.abort();
        reject(new DOMException('Aborted', 'AbortError'));
      };
      if (signal) signal.addEventListener('abort', onAbort, { once: true });
      const primarySet = new Set(APIS);
      let primaryPending = candidates.filter(
        (candidate) => candidate.type === 'piped' && primarySet.has(candidate.base)
      ).length;
      const scheduleGrace = (delay) => {
        clearTimeout(graceTimer);
        graceTimer = setTimeout(() => {
          if (!finished && best) finish(best.video);
        }, delay);
      };
      const finish = (video) => {
        if (finished) return;
        finished = true;
        if (best && best.candidate) {
          lastSource = { type: best.candidate.type, base: best.candidate.base };
          video.streamSource = best.candidate.type;
          video.streamOrigin = sourceHost(best.candidate.base);
          try { localStorage.setItem('youtube:last-source', JSON.stringify(lastSource)); } catch (e) {}
        }
        cleanup();
        resolve(video);
      };
      const consider = (video, candidate) => {
        const rank = candidate.type === 'piped' ? (video.hls ? 3 : 2) : 1;
        if (!best || rank > best.rank) best = { video, rank, candidate };
        if (rank === 3) {
          finish(video);
          return;
        }
        scheduleGrace(primaryPending > 0 ? 1800 : 400);
      };
      if (!candidates.length) {
        fail();
        return;
      }
      let index = 0;
      const worker = async () => {
        while (!finished && index < candidates.length) {
          const candidate = candidates[index++];
          const controller = new AbortController();
          controllers.push(controller);
          try {
            const video = candidate.type === 'piped'
              ? await fetchPipedCandidate(candidate.base, id, controller.signal)
              : await fetchInvidiousCandidate(candidate.base, id, controller.signal);
            if (!finished) consider(video, candidate);
          } catch (e) {
            // ignore individual failures
          } finally {
            if (candidate.type === 'piped' && primarySet.has(candidate.base)) {
              primaryPending -= 1;
              if (primaryPending === 0 && !finished && best && best.rank < 3) {
                scheduleGrace(400);
              }
            }
            settled += 1;
            if (!finished && settled === candidates.length) {
              if (best) finish(best.video);
              else fail();
            }
          }
        }
      };
      const concurrency = Math.min(12, candidates.length);
      for (let i = 0; i < concurrency; i += 1) worker();
    });
  }

  async function loadStream(id, signal, onPreview) {
    if (signal && signal.aborted) throw new DOMException('Aborted', 'AbortError');
    // Start the fallback now so it is already warm if Yattee fails, but do not
    // let it win while Yattee is still working. Yattee is the preferred source.
    // Public metadata can still paint the page immediately while Yattee is
    // deciding, so Yattee never holds up the page itself.
    const publicJob = loadPublicStream(id, signal).then(
      (video) => {
        if (video && !video.streamSource) {
          video.streamSource = lastSource ? lastSource.type : 'piped';
          video.streamOrigin = lastSource ? sourceHost(lastSource.base) : '';
        }
        if (onPreview) {
          try { onPreview(video); } catch (e) {}
        }
        return { video };
      },
      (error) => ({ error })
    );

    if (yatteeOnly()) {
      if (!yatteeEnabled()) {
        throw new Error('Yattee source is forced, but no Yattee credentials are configured.');
      }
      const controller = new AbortController();
      const abort = () => controller.abort();
      if (signal) signal.addEventListener('abort', abort, { once: true });
      try {
        const yattee = await fetchYatteeStream(id, controller.signal).catch(() => null);
        if (signal && signal.aborted) throw new DOMException('Aborted', 'AbortError');
        if (!yattee) throw new Error('Yattee is the forced source, but it did not return a stream.');
        yattee.streamSource = 'yattee';
        yattee.streamOrigin = sourceHost(yatteeConfig().url);
        return yattee;
      } finally {
        controller.abort();
        if (signal) signal.removeEventListener('abort', abort);
      }
    }

    if (yatteeEnabled()) {
      const controller = new AbortController();
      const abort = () => controller.abort();
      if (signal) signal.addEventListener('abort', abort, { once: true });
      const yatteePromise = fetchYatteeStream(id, controller.signal).catch(() => null);
      try {
        // Decide from the public lookup first. Live never waits on Yattee:
        // its relay is slower and live is available directly.
        const publicResult = await publicJob;
        if (signal && signal.aborted) throw new DOMException('Aborted', 'AbortError');
        if (publicResult.video && publicResult.video.live) {
          controller.abort();
          return publicResult.video;
        }

        const yattee = await yatteePromise;
        if (signal && signal.aborted) throw new DOMException('Aborted', 'AbortError');
        if (yattee) {
          yattee.streamSource = 'yattee';
          yattee.streamOrigin = sourceHost(yatteeConfig().url);
          publicFallbacks.set(id, Promise.resolve(publicResult.video || null));
          if (publicFallbacks.size > 10) {
            publicFallbacks.delete(publicFallbacks.keys().next().value);
          }
          return yattee;
        }
        if (publicResult.video) return publicResult.video;
        throw publicResult.error || new Error('No playable stream');
      } finally {
        controller.abort();
        if (signal) signal.removeEventListener('abort', abort);
      }
    }

    try {
      const fallback = await publicJob;
      if (signal && signal.aborted) throw new DOMException('Aborted', 'AbortError');
      if (fallback.video) return fallback.video;
      throw fallback.error || new Error('No playable stream');
    } catch (e) {
      if (signal && signal.aborted) {
        throw new DOMException('Aborted', 'AbortError');
      }
      throw e instanceof Error ? e : new Error('No playable stream');
    }
  }

  const isListPayload = (data) =>
    Array.isArray(data) || (data && Array.isArray(data.items));

  async function cachedRace(path, signal) {
    const cached = listCache.get(path);
    if (cached && Date.now() - cached.time < 120000) return cached.data;
    const data = await apiRace(path, isListPayload, signal);
    listCache.set(path, { data, time: Date.now() });
    if (listCache.size > 30) listCache.delete(listCache.keys().next().value);
    return data;
  }

  function loadHls() {
    if (window.Hls) return Promise.resolve(window.Hls);
    if (hlsPromise) return hlsPromise;
    hlsPromise = new Promise((resolve, reject) => {
      const sources = [
        'https://cdn.jsdelivr.net/npm/hls.js@1.7.3/dist/hls.min.js',
        'https://unpkg.com/hls.js@1.7.3/dist/hls.min.js'
      ];
      let index = 0;
      const next = () => {
        if (index >= sources.length) {
          hlsPromise = null;
          reject(new Error('HLS unavailable'));
          return;
        }
        const script = document.createElement('script');
        script.src = sources[index++];
        script.async = true;
        script.onload = () => {
          if (window.Hls) resolve(window.Hls);
          else next();
        };
        script.onerror = () => {
          script.remove();
          next();
        };
        document.head.appendChild(script);
      };
      next();
    });
    return hlsPromise;
  }

  function updateNav(type, query = '') {
    const key = type === 'home'
      ? 'home'
      : type === 'search'
        ? `q:${String(query).trim().toLowerCase()}`
        : type === 'playlist'
          ? `playlist:${query}`
          : type === 'saved'
            ? 'saved'
            : type === 'settings'
              ? 'settings'
              : '';
    document.querySelectorAll('[data-nav-key]').forEach((item) => {
      item.classList.toggle('active', item.dataset.navKey === key);
    });
  }

  function closeGuide() {
    document.body.classList.remove('guide-open');
  }

  async function homeView(seq, signal) {
    view.innerHTML = chipsHTML() + skeletonGrid();
    const paths = [
      `/trending?region=${encodeURIComponent(REGION)}`,
      '/search?q=trending%20videos&filter=videos'
    ];
    let items = [];
    for (const path of paths) {
      try {
        const data = await cachedRace(path, signal);
        items = normalizeItems(data);
        if (items.length) break;
      } catch (e) {
        if (signal.aborted) return;
      }
    }
    if (seq !== routeSeq) return;
    document.title = 'YouTube';
    if (!items.length) {
      view.innerHTML = chipsHTML() + errorStateHTML(
        'Unable to load videos',
        'The public video servers did not respond. Please try again.'
      );
      return;
    }
    view.innerHTML = chipsHTML() + `<div class="grid">${items.map(cardHTML).join('')}</div>`;
  }

  const liveLookupCache = new Map();

  function searchKey(value) {
    return String(value || '').toLowerCase()
      .normalize('NFD').replace(/[\u0300-\u036f]/g, '')
      .replace(/[^a-z0-9]+/g, ' ').trim();
  }

  function channelIDFromURL(url) {
    const match = String(url || '').match(/\/channel\/([A-Za-z0-9_-]+)/);
    return match ? match[1] : '';
  }

  function channelMatchScore(query, name) {
    const key = searchKey(name);
    if (!key) return 0;
    if (key === query) return 100;
    if (key.startsWith(query + ' ') || query.startsWith(key + ' ')) return 75;
    const wanted = new Set(query.split(' '));
    const words = new Set(key.split(' '));
    let hits = 0;
    for (const word of wanted) if (words.has(word)) hits += 1;
    return hits === wanted.size ? 60 : 0;
  }

  async function fetchChannelLivePrimary(tabData, signal) {
    for (const base of APIS) {
      try {
        const response = await fetch(
          `${base}/channels/tabs?data=${encodeURIComponent(tabData)}`,
          {
            signal,
            cache: 'no-store',
            priority: 'high',
            headers: { Accept: 'application/json' }
          }
        );
        if (!response.ok) continue;
        const data = await response.json();
        const items = (data.content || [])
          .map(normalizeItem)
          .filter((video) => video && video.id);
        if (items.length) return items;
      } catch (e) {
        if (signal && signal.aborted) return [];
      }
    }
    return [];
  }

  async function discoverChannelLive(query, items, signal) {
    const key = searchKey(query);
    if (!key || key.split(' ').length > 6) return { matched: false, items: [] };
    const cached = liveLookupCache.get(key);
    if (cached && Date.now() - cached.at < 60000) return cached.result;

    const remember = (result) => {
      liveLookupCache.set(key, { at: Date.now(), result });
      if (liveLookupCache.size > 20) {
        liveLookupCache.delete(liveLookupCache.keys().next().value);
      }
      return result;
    };

    try {
      let best = 0;
      let channelID = '';
      for (const item of items) {
        const id = channelIDFromURL(item.uploaderUrl);
        if (!id) continue;
        const score = channelMatchScore(key, item.channel);
        if (score > best) {
          best = score;
          channelID = id;
        }
      }
      if (!channelID || best < 70) {
        const data = await cachedRace(
          `/search?q=${encodeURIComponent(query)}&filter=channels`,
          signal
        );
        const channels = data && Array.isArray(data.items) ? data.items : [];
        for (const channel of channels) {
          const id = channelIDFromURL(channel.url);
          if (!id) continue;
          let score = channelMatchScore(key, channel.name);
          if (channel.verified) score += 5;
          if (score > best) {
            best = score;
            channelID = id;
          }
        }
      }
      if (!channelID || best < 50) return remember({ matched: false, items: [] });

      const channel = await fetchChannel(channelID, signal);
      if (!channel) return remember({ matched: false, items: [] });
      const strong = best >= 100 && Number(channel.subscribers) >= 100000;
      const activeVideos = channel.videos
        .filter((video) => video.live && Number(video.views) >= 0 && !video.when)
        .slice(0, 3);
      if (activeVideos.length) {
        return remember({ matched: strong, items: activeVideos, channelName: channel.name });
      }
      const tab = (channel.tabs || []).find((entry) => /live/i.test(entry.name || ''));
      if (!tab || !tab.data) {
        return remember({ matched: strong, items: [], channelName: channel.name });
      }
      const live = await fetchChannelLivePrimary(tab.data, signal);
      const active = live
        .filter((video) => video.live && Number(video.views) > 0 && !video.when)
        .slice(0, 3);
      return remember({ matched: strong, items: active, channelName: channel.name });
    } catch (e) {
      if (signal && signal.aborted) return { matched: false, items: [] };
      return remember({ matched: false, items: [] });
    }
  }

  async function searchView(query, seq, signal) {
    searchInput.value = query;
    view.innerHTML = `<div class="results-page">
      <h1 class="search-heading">Results for “${esc(query)}”</h1>
      ${skeletonResults()}
    </div>`;
    try {
      const data = await cachedRace(`/search?q=${encodeURIComponent(query)}&filter=videos`, signal);
      if (seq !== routeSeq) return;
      const items = normalizeItems(data);
      document.title = `${query} - YouTube`;
      if (!items.length) {
        view.innerHTML = `<div class="results-page">
          <h1 class="search-heading">Results for “${esc(query)}”</h1>
          ${stateHTML('No videos found', 'Try a different search, or paste a YouTube link.')}
        </div>`;
        return;
      }
      const paintResults = (videos) => {
        const liveItems = videos.filter((item) => item.live);
        const otherItems = videos.filter((item) => !item.live);
        const liveSection = liveItems.length
          ? `<h2 class="section-heading">Live now</h2>
            <div class="result-list">${liveItems.map(resultHTML).join('')}</div>`
          : '';
        const videoHeading = liveItems.length && otherItems.length
          ? '<h2 class="section-heading">Videos</h2>'
          : '';
        const scrollY = window.scrollY;
        view.innerHTML = `<div class="results-page">
          <h1 class="search-heading">Results for “${esc(query)}”</h1>
          ${liveSection}
          ${videoHeading}
          <div class="result-list">${otherItems.map(resultHTML).join('')}</div>
        </div>`;
        window.scrollTo(0, scrollY);
      };
      paintResults(items);

      discoverChannelLive(query, items, signal).then((result) => {
        if (!result || !result.matched || seq !== routeSeq || signal.aborted) return;
        const seen = new Set();
        const channelKey = searchKey(result.channelName || '');
        const keepSearchLive = (item) => {
          if (!item.live) return false;
          if (!channelKey) return true;
          return searchKey(item.channel) === channelKey;
        };
        const live = [...result.items, ...items.filter(keepSearchLive)].filter((item) => {
          if (seen.has(item.id)) return false;
          seen.add(item.id);
          return true;
        });
        const videos = items.filter((item) => {
          if (item.live || seen.has(item.id)) return false;
          seen.add(item.id);
          return true;
        });
        paintResults([...live, ...videos]);
      }).catch(() => {});
    } catch (e) {
      if (seq !== routeSeq || signal.aborted) return;
      view.innerHTML = `<div class="results-page">
        <h1 class="search-heading">Results for “${esc(query)}”</h1>
        ${errorStateHTML('Search unavailable', 'The public video servers did not respond. Please try again.')}
      </div>`;
    }
  }

  function watchSkeletonHTML() {
    return `<div class="watch-page">
      <div class="watch-primary">
        <div class="player-loading"><div class="spinner"></div></div>
        <div class="sk sk-line title" style="height:24px;width:78%;margin:16px 0 12px"></div>
        <div class="watch-toolbar">
          <div class="owner">
            <div class="sk sk-avatar" style="width:40px;height:40px"></div>
            <div>
              <div class="sk sk-line" style="width:150px"></div>
              <div class="sk sk-line short" style="width:100px;margin:0"></div>
            </div>
          </div>
          <div class="sk sk-line" style="width:260px;height:36px;border-radius:18px;margin:0"></div>
        </div>
        <div class="sk" style="height:110px;border-radius:12px;margin-top:14px"></div>
      </div>
      <aside class="related">
        <div class="related-head">Up next</div>
        <div class="related-list">${skeletonCompactList()}</div>
      </aside>
    </div>`;
  }

  function watchErrorHTML(id) {
    return `<div class="error-page">
      ${stateHTML(
        'Video unavailable',
        'This video could not be loaded. It may be private, age-restricted, or temporarily unavailable from the public video servers.',
        `<button class="btn" type="button" data-retry>${icon('refresh')}<span>Try again</span></button>`
      )}
    </div>`;
  }

  function playerControlsHTML(video) {
    return `<button class="player-center" id="playerCenter" type="button" aria-label="Play">
        ${icon('play')}
      </button>
      <div class="player-controls" id="playerControls">
        ${video.live ? '' : '<input class="player-seek" id="playerSeek" type="range" min="0" max="1000" step="1" value="0" aria-label="Seek">'}
        <div class="player-control-row">
          <button class="player-btn" id="playerPlay" type="button" aria-label="Play">
            ${icon('play')}
          </button>
          ${video.live ? '' : `<button class="player-btn" id="playerBack" type="button" aria-label="Back 10 seconds">
            ${icon('back10')}
          </button>
          <button class="player-btn" id="playerForward" type="button" aria-label="Forward 10 seconds">
            ${icon('forward10')}
          </button>`}
          <span class="player-time" id="playerTime">
            <span id="playerCurrent">0:00</span><span class="player-time-sep"> / </span><span id="playerDuration">0:00</span>
          </span>
        </div>
      </div>`;
  }

  function watchHTML(video) {
    const meta = [
      video.live ? 'Live now' : '',
      video.views >= 0 ? (video.live ? `${fmtCount(video.views)} watching` : fmtViews(video.views)) : '',
      video.when && !video.live ? video.when : ''
    ].filter(Boolean).join(' • ');
    const subscribers = video.subscribers >= 0
      ? `${fmtCount(video.subscribers)} subscribers`
      : 'YouTube channel';
    const related = video.related.length
      ? `<div class="related-list">${video.related.map(compactHTML).join('')}</div>`
      : stateHTML('No related videos', 'This stream has no related videos to show.');
    return `<div class="watch-page">
      <div class="watch-primary">
        <div class="player-shell is-paused${video.live ? ' is-live' : ''}">
          <video id="playerVideo" playsinline preload="metadata"${!video.live && savedMuted() ? ' muted' : ''}></video>
          <canvas class="player-canvas" id="playerCanvas" hidden></canvas>
          <img class="player-poster" id="playerPoster" src="https://i.ytimg.com/vi/${video.id}/maxresdefault.jpg" alt="" draggable="false" referrerpolicy="no-referrer">
          <div class="player-status" id="playerStatus">
            <div class="spinner"></div>
          </div>
          ${playerControlsHTML(video)}
        </div>
        <h1 class="watch-title">${esc(video.title)}</h1>
        <div class="watch-toolbar">
          <div class="owner">
            <a class="owner-avatar" href="${esc(channelURL(video))}" data-nav title="Visit channel">${avatarHTML(video.channel, video.avatar)}</a>
            <div class="owner-text">
              <div class="owner-line">
                <a class="owner-name" href="${esc(channelURL(video))}" data-nav title="Visit channel">${esc(video.channel)}</a>
                ${video.live ? '<span class="live-badge">LIVE</span>' : ''}
              </div>
              <div class="owner-sub">${esc(subscribers)}</div>
            </div>
          </div>
          <div class="actions">
            <button class="action" id="saveBtn" type="button" title="Save" aria-label="Save" aria-pressed="false">
              ${icon('save')}<span>Save</span>
            </button>
            <button class="action" id="muteBtn" type="button" title="Mute" aria-label="Mute" aria-pressed="false">
              ${icon('volume')}<span>Mute</span>
            </button>
            <button class="action" id="repeatBtn" type="button" title="Repeat" aria-label="Repeat" aria-pressed="false">
              ${icon('repeat')}<span>Repeat</span>
            </button>
            <button class="action quality-badge" id="qualityBtn" type="button" title="Refresh stream" aria-label="Refresh stream">
              ${icon('screen')}<span id="qualityText">${esc(fmtQuality(video.quality?.height))}</span>
            </button>
          </div>
        </div>
        <div class="description">
          <div class="desc-meta">${esc(meta || 'Ad-free stream')}</div>
          <p class="desc-text" id="descText">${esc(video.description || 'No description.')}</p>
          <button class="desc-toggle" id="descToggle" type="button" aria-expanded="false" hidden>...more</button>
        </div>
      </div>
      <aside class="related">
        <div class="related-head">Up next</div>
        ${related}
      </aside>
    </div>`;
  }



  function savedMuted() {
    try { return localStorage.getItem('youtube:muted') === '1'; } catch (e) { return false; }
  }

  function setSavedMuted(muted) {
    try { localStorage.setItem('youtube:muted', muted ? '1' : '0'); } catch (e) {}
  }

  function engineAudioActive() {
    return !!(currentEngine && currentEngine.live && !currentEngine.live.videoOnly);
  }

  function updateMuteButton() {
    const button = $('#muteBtn');
    if (!button) return;
    const player = $('#playerVideo');
    let muted;
    if (engineAudioActive()) {
      muted = currentEngine.muted;
    } else if (currentVideo && currentVideo.live) {
      // Live uses the engine for audio; the native element is intentionally
      // muted. Reflect the saved user state until engine audio is active.
      muted = savedMuted();
    } else {
      muted = !player || player.muted || player.volume === 0;
    }
    button.innerHTML = `${icon(muted ? 'muted' : 'volume')}<span>${muted ? 'Unmute' : 'Mute'}</span>`;
    button.title = muted ? 'Unmute' : 'Mute';
    button.setAttribute('aria-label', muted ? 'Unmute' : 'Mute');
    button.setAttribute('aria-pressed', String(muted));
    button.classList.toggle('active', muted);
  }

  function wireWatch(video) {
    currentVideo = video;
    const saveBtn = $('#saveBtn');
    const muteBtn = $('#muteBtn');
    const qualityBtn = $('#qualityBtn');
    const repeatBtn = $('#repeatBtn');
    const getPlayer = () => $('#playerVideo');
    const descText = $('#descText');
    const descToggle = $('#descToggle');
    let saved = isSaved(video.id);

    const paintSave = () => {
      saveBtn.classList.toggle('active', saved);
      saveBtn.setAttribute('aria-pressed', String(saved));
      saveBtn.title = saved ? 'Remove from Saved' : 'Save';
      saveBtn.setAttribute('aria-label', saved ? 'Remove from Saved' : 'Save');
      saveBtn.innerHTML = `${icon('save')}<span>${saved ? 'Saved' : 'Save'}</span>`;
    };

    saveBtn.addEventListener('click', () => {
      if (saved) {
        openConfirm(
          'Remove from Saved?',
          `Remove "${video.title}" from your Saved list?`,
          'Remove',
          () => {
            removeSaved(video.id);
            saved = false;
            paintSave();
          }
        );
        return;
      }
      addSaved(video);
      saved = true;
      paintSave();
    });
    paintSave();

    if (qualityBtn) {
      qualityBtn.addEventListener('click', () => location.reload());
    }

    if (muteBtn) {
      muteBtn.addEventListener('click', () => {
        if (engineAudioActive()) {
          currentEngine.setMuted(!currentEngine.muted);
          if (!currentEngine.muted) currentEngine.unlock();
          setSavedMuted(currentEngine.muted);
          updateMuteButton();
          return;
        }
        const active = getPlayer();
        if (!active) return;
        active.muted = !active.muted;
        if (!active.muted && active.volume === 0) active.volume = 0.5;
        setSavedMuted(active.muted);
        updateMuteButton();
      });
      const initial = getPlayer();
      if (initial) initial.addEventListener('volumechange', updateMuteButton);
      updateMuteButton();
    }

    if (repeatBtn) {
      const repeatKey = `dltube:loop:${video.id}`;
      let looping = false;
      try {
        looping = localStorage.getItem(repeatKey) === '1';
      } catch (e) {}
      const paintRepeat = () => {
        repeatBtn.classList.toggle('active', looping);
        repeatBtn.setAttribute('aria-pressed', String(looping));
        repeatBtn.title = looping ? 'Repeat on' : 'Repeat';
        repeatBtn.setAttribute('aria-label', looping ? 'Repeat on' : 'Repeat');
      };
      const initialPlayer = getPlayer();
      if (initialPlayer) initialPlayer.loop = looping;
      repeatBtn.addEventListener('click', () => {
        looping = !looping;
        const active = getPlayer();
        if (active) active.loop = looping;
        try {
          if (looping) localStorage.setItem(repeatKey, '1');
          else localStorage.removeItem(repeatKey);
        } catch (e) {}
        paintRepeat();
      });
      paintRepeat();
    }

    if (video.description.length > 260) {
      descText.classList.add('collapsed');
      descToggle.hidden = false;
      descToggle.addEventListener('click', () => {
        const open = descText.classList.toggle('collapsed');
        descToggle.textContent = open ? '...more' : 'Show less';
        descToggle.setAttribute('aria-expanded', String(!open));
      });
    }
  }

  function teardownPlayback() {
    const player = $('#playerVideo');
    if (player) {
      try { player.pause(); } catch (e) {}
    }
    if (currentHls) {
      try { currentHls.destroy(); } catch (e) {}
      currentHls = null;
    }
    if (currentEngine) {
      try { currentEngine.destroy(); } catch (e) {}
      currentEngine = null;
    }
    if (currentEngineSyncTimer) clearInterval(currentEngineSyncTimer);
    currentEngineSyncTimer = 0;
    if (currentEnginePlayer && currentEngineSeekHandler) {
      currentEnginePlayer.removeEventListener('seeked', currentEngineSeekHandler);
    }
    currentEnginePlayer = null;
    currentEngineSeekHandler = null;
  }

  function showPlayerErrorNow(message, video) {
    const status = $('#playerStatus');
    if (!status) return;
    const teslaBadge = $('#teslaBadge');
    if (teslaBadge) teslaBadge.hidden = true;
    const player = $('#playerVideo');
    const surface = player || $('#playerCanvas');
    if (surface) {
      const shell = surface.closest('.player-shell');
      if (shell) shell.classList.add('is-error');
    }
    teardownPlayback();
    status.hidden = false;
    status.innerHTML = `${icon('alert')}
      <div class="status-title">Playback unavailable</div>
      <div class="status-detail">${esc(message)}</div>
      <div class="status-actions">
        <button class="btn" type="button" data-retry>${icon('refresh')}<span>Try again</span></button>
        <a class="btn ghost" href="https://www.youtube.com/watch?v=${encodeURIComponent(video.id)}" target="_blank" rel="noopener">${icon('external')}<span>YouTube</span></a>
      </div>`;
  }

  function showPlayerError(message, video) {
    if (video && currentVideo && video !== currentVideo) return;
    if (video && video.streamSource === 'yattee' && yatteeOnly()) {
      showPlayerErrorNow(message, video);
      return;
    }
    if (video && video.streamSource === 'yattee' && !fallbackAttempts.has(video)) {
      fallbackAttempts.add(video);
      const seq = routeSeq;
      const startAt = video.live
        ? 0
        : Math.max(0, Number($('#playerVideo') && $('#playerVideo').currentTime) || 0);
      teardownPlayback();
      const status = $('#playerStatus');
      if (status) {
        status.hidden = false;
        status.innerHTML = `${icon('refresh')}
          <div class="status-title">Switching to backup source…</div>
          <div class="status-detail">The Yattee stream failed; trying the public stream.</div>`;
      }
      const fallback = publicFallbacks.get(video.id) ||
        loadPublicStream(video.id, routeAbort && routeAbort.signal).catch(() => null);
      Promise.resolve(fallback).then((alternate) => {
        if (seq !== routeSeq) return;
        if (!alternate) {
          showPlayerErrorNow(message, video);
          return;
        }
        publicFallbacks.delete(video.id);
        if (!alternate.streamSource) {
          alternate.streamSource = lastSource ? lastSource.type : 'piped';
          alternate.streamOrigin = lastSource ? sourceHost(lastSource.base) : '';
        }
        currentVideo = alternate;
        teardownPlayback();
        view.innerHTML = watchHTML(alternate);
        document.title = `${alternate.title} - YouTube`;
        wireWatch(alternate);
        startPlayer(alternate, startAt, seq);
      }).catch(() => {
        if (seq === routeSeq) showPlayerErrorNow(message, video);
      });
      return;
    }
    showPlayerErrorNow(message, video);
  }

  function findOriginalAudioIndex(tracks, video) {
    const names = tracks.map((track) => String(track.name || ''));
    let index = names.findIndex((name) => /original/i.test(name) && !/dub/i.test(name));
    if (index >= 0) return index;

    if (video.originalAudio) {
      const originalName = String(video.originalAudio.name || '')
        .replace(/\s*[-–—]?\s*original\s*$/i, '')
        .trim()
        .toLowerCase();
      if (originalName) {
        index = names.findIndex(
          (name) => name.toLowerCase().includes(originalName) && !/dub/i.test(name)
        );
      }
      if (index < 0 && video.originalAudio.lang) {
        const lang = String(video.originalAudio.lang).toLowerCase();
        index = tracks.findIndex((track) => {
          const trackLang = String(track.lang || '').toLowerCase();
          return trackLang === lang || trackLang.split('-')[0] === lang.split('-')[0];
        });
      }
    }

    if (index < 0 && names.some((name) => /dub/i.test(name))) {
      index = names.findIndex((name) => !/dub/i.test(name));
    }
    return index;
  }

  function useOriginalAudio(hls, video) {
    const tracks = hls.audioTracks || [];
    if (tracks.length < 2) return;
    const index = findOriginalAudioIndex(tracks, video);
    if (index >= 0 && hls.audioTrack !== index) hls.audioTrack = index;
  }

  function updateQualityFromLevels(hls) {
    let bestIndex = -1;
    let bestHeight = 0;
    let bestFps = 0;
    const limit = maxDefinition();
    (hls.levels || []).forEach((level, index) => {
      const height = Number(level.height) || 0;
      if (height <= 0 || height > limit) return;
      const fps = Number(level.attrs?.['FRAME-RATE']) || Number(level.frameRate) || 0;
      if (height > bestHeight || (height === bestHeight && fps > bestFps)) {
        bestIndex = index;
        bestHeight = height;
        bestFps = fps;
      }
    });
    if (bestIndex < 0) return;
    hls.autoLevelCapping = bestIndex;
    updateQualityBadge(bestHeight, bestFps);
  }

  function loadScriptOnce(src) {
    return new Promise((resolve, reject) => {
      if (document.querySelector(`script[data-src="${src}"]`)) { resolve(); return; }
      const script = document.createElement('script');
      script.src = src;
      script.async = true;
      script.dataset.src = src;
      script.onload = () => resolve();
      script.onerror = () => reject(new Error(`Could not load ${src}`));
      document.head.appendChild(script);
    });
  }

  let teslaLibsPromise = null;
  function preloadTeslaLibs() {
    if (!teslaLibsPromise) {
      teslaLibsPromise = Promise.all([
        loadScriptOnce('https://cdn.jsdelivr.net/npm/mux.js@7.1.0/dist/mux.min.js'),
        loadScriptOnce('https://cdn.jsdelivr.net/npm/mp4box@0.5.2/dist/mp4box.all.min.js')
      ]).catch((e) => {
        teslaLibsPromise = null;
        throw e;
      });
    }
    return teslaLibsPromise;
  }

  function teslaEnginePreferred() {
    return true;
  }

  function isTeslaBrowser() {
    return /Tesla/i.test(navigator.userAgent || '');
  }

  async function startTeslaEngine(video, startAt, seq) {
    const player = $('#playerVideo');
    const canvas = $('#playerCanvas');
    const status = $('#playerStatus');
    const poster = $('#playerPoster');
    const shell = player && player.closest('.player-shell');
    if (!player || !canvas || !shell) return;
    const hlsPreload = video.hls ? loadHls().catch(() => null) : Promise.resolve(null);
    try {
      await Promise.all([preloadTeslaLibs(), hlsPreload]);
    } catch (e) {
      showPlayerError('The Tesla player libraries could not be loaded.', video);
      return;
    }
    if (seq !== routeSeq || !window.TeslaPlayer) {
      if (seq === routeSeq) showPlayerError('The Tesla player is unavailable.', video);
      return;
    }
    shell.classList.add('engine-mode');
    player.hidden = false;
    canvas.hidden = false;
    setupPlayerControls(player, video);
    const showStart = () => {
      if (seq !== routeSeq) return;
      if (status) status.hidden = true;
      if (poster) poster.hidden = false;
      shell.classList.remove('controls-hidden', 'is-error');
      shell.classList.add('is-paused');
    };
    const startMuted = (error) => {
      if (seq !== routeSeq) return;
      if (video.live) {
        player.play().catch(showStart);
        return;
      }
      if (error && error.name !== 'NotAllowedError') {
        setTimeout(() => {
          if (seq === routeSeq) player.play().catch(showStart);
        }, 200);
        return;
      }
      // Chrome refused audible autoplay. Follow policy with muted playback;
      // the user can unmute explicitly when they are ready.
      player.muted = true;
      updateMuteButton();
      player.play().catch(showStart);
    };
    canvas.addEventListener('click', () => {
      if (player.paused) player.play().catch(() => {});
      else player.pause();
    });

    const wasMuted = savedMuted();
    // The native element owns VOD audio, while live audio comes from the
    // engine. Keep the unused path muted, but never mute the audible path just
    // because a new video is loading.
    player.muted = video.live ? true : wasMuted;
    if (video.hls) {
      const Hls = await hlsPreload;
      if (!Hls || !Hls.isSupported()) {
        showPlayerError('HLS audio playback is unsupported in this browser.', video);
        return;
      }
      const config = {
        enableWorker: true,
        capLevelToPlayerSize: false,
        maxBufferLength: video.live ? 20 : 30,
        backBufferLength: 20
      };
      if (video.live) {
        config.liveSyncDurationCount = 3;
        config.liveMaxLatencyDurationCount = 10;
      }
      const hls = new Hls(config);
      currentHls = hls;
      hls.on(Hls.Events.MANIFEST_PARSED, () => {
        if (seq !== routeSeq) return;
        useOriginalAudio(hls, video);
        // The media element under the canvas is the audio clock. Keep its
        // hidden video decode at the lowest level; TeslaEngine paints the
        // visible, higher-quality frames independently.
        if (hls.levels && hls.levels.length) {
          let lowest = 0;
          let lowestHeight = Infinity;
          hls.levels.forEach((level, index) => {
            const height = Number(level.height) || 0;
            if (height > 0 && height < lowestHeight) {
              lowest = index;
              lowestHeight = height;
            }
          });
          hls.autoLevelCapping = lowest;
          hls.startLevel = lowest;
        }
        const seek = () => {
          if (startAt > 0 && !video.live) {
            try { player.currentTime = startAt; } catch (e) {}
          }
        };
        if (player.readyState >= 1) seek();
        else player.addEventListener('loadedmetadata', seek, { once: true });
        player.play().catch(startMuted);
      });
      hls.on(Hls.Events.AUDIO_TRACKS_UPDATED, () => {
        if (seq === routeSeq) useOriginalAudio(hls, video);
      });
      hls.on(Hls.Events.AUDIO_TRACK_SWITCHED, () => {
        if (seq === routeSeq) useOriginalAudio(hls, video);
      });
      hls.on(Hls.Events.ERROR, (_, data) => {
        if (seq === routeSeq && data && data.fatal) {
          showPlayerError('HLS audio playback failed: ' + (data.details || data.type), video);
        }
      });
      hls.attachMedia(player);
      hls.loadSource(video.hls);
    } else {
      player.src = video.source;
      if (startAt > 0) {
        player.addEventListener('loadedmetadata', () => {
          try { player.currentTime = startAt; } catch (e) {}
        }, { once: true });
      }
      player.play().catch(startMuted);
    }

    const engine = new window.TeslaPlayer({ canvas, maxWidth: 1280, maxHeight: maxDefinition(), gain: 1 });
    currentEngine = engine;
    engine.setMuted(wasMuted);
    updateMuteButton();
    if (video.live) {
      setTimeout(() => {
        if (seq === routeSeq && !player.paused &&
            engine.actx && engine.actx.state !== 'running') {
          engine.setMuted(true);
          player.dispatchEvent(new Event('volumechange'));
        }
      }, 1200);
      player.dispatchEvent(new Event('volumechange'));
    }
    player.addEventListener('pause', () => {
      engine.setVideoPaused(true);
      if (video.live && engine.actx) engine.actx.suspend().catch(() => {});
    });
    player.addEventListener('playing', () => {
      engine.setVideoPaused(false);
      if (video.live) engine.unlock();
    });
    const engineUrl = video.hls || video.source;
    const engineMeta = { name: video.title, startAt: startAt || 0, fileUrl: !video.hls, videoOnly: !video.live, live: !!video.live };
    const avParam = new URLSearchParams(location.search).get('av');
    let avOffset = Number(avParam);
    if (!Number.isFinite(avOffset)) avOffset = 0;
    try { localStorage.removeItem('youtube:av-offset'); } catch (e) {}
    const avOffsetS = avOffset / 1000;
    let syncAudioBase = null;
    let syncEngineBase = null;
    let lastAudioTime = null;
    let syncStallSince = 0;
    let pausedForSync = false;
    let lastDrawnCount = -1;
    let lastDrawnAt = Date.now();
    let liveFreeRun = false;
    let presentedMediaTime = NaN;
    let presentedAt = 0;
    let presentedRate = 1;
    const statusTitle = status && status.querySelector('.status-title');
    const onPresentedFrame = (now, metadata) => {
      if (!metadata) return;
      presentedMediaTime = Number(metadata.mediaTime);
      presentedAt = Number(metadata.expectedDisplayTime) || now;
      presentedRate = Number(player.playbackRate) || 1;
      if (seq === routeSeq) player.requestVideoFrameCallback(onPresentedFrame);
    };
    if ('requestVideoFrameCallback' in player) player.requestVideoFrameCallback(onPresentedFrame);
    const syncClock = () => {
      if (!engine.live) return NaN;
      const nowPerf = performance.now();
      let audioTime = Number(player.currentTime);
      if (Number.isFinite(presentedMediaTime) && nowPerf - presentedAt < 1200) {
        audioTime = presentedMediaTime + ((nowPerf - presentedAt) / 1000) * presentedRate;
      }
      const state = engine.state();
      const engineTime = Number(state.currentTime);
      if (state.stage === 'idle' || !Number.isFinite(audioTime) || !Number.isFinite(engineTime)) return NaN;
      // VOD uses the same media timeline in both pipelines: target the audio
      // time directly. A baseline here would freeze the startup gap between
      // the canvas and the audio into a permanent lip-sync offset.
      if (!video.live) {
        lastAudioTime = audioTime;
        return audioTime + avOffsetS;
      }
      if (syncAudioBase === null || (lastAudioTime !== null && audioTime < lastAudioTime - 1)) {
        syncAudioBase = audioTime;
        syncEngineBase = engineTime;
      }
      lastAudioTime = audioTime;
      return syncEngineBase + (audioTime - syncAudioBase) + avOffsetS;
    };
    const syncCanvas = () => {
      const targetTime = syncClock();
      if (!Number.isFinite(targetTime)) return;
      if (!video.live) engine.syncTo(targetTime);
      const state = engine.state();
      if (video.live && !liveFreeRun && !player.paused &&
          state.drawn === lastDrawnCount && Date.now() - lastDrawnAt > 3000) {
        liveFreeRun = true;
        engine.setClock(null);
      }
      if (state.drawn !== lastDrawnCount) {
        lastDrawnCount = state.drawn;
        lastDrawnAt = Date.now();
      }
      if (video.hls && !video.live) {
        const buffered = Number(state.buffered) || 0;
        if (!player.paused && buffered < 0.25) {
          if (!syncStallSince) syncStallSince = Date.now();
          if (!pausedForSync && Date.now() - syncStallSince > 1500) {
            pausedForSync = true;
            if (statusTitle) statusTitle.textContent = 'Buffering video to keep audio in sync…';
            if (status) status.hidden = false;
            player.pause();
          }
        } else if (buffered > 0.5) {
          syncStallSince = 0;
          if (player.paused && pausedForSync && buffered > 1) {
            pausedForSync = false;
            if (status) status.hidden = true;
            player.play().catch(() => {});
          }
        }
      }
    };
    const reopenCanvasAt = () => {
      if (video.live || seq !== routeSeq) return;
      const at = Math.max(0, Number(player.currentTime) || 0);
      syncAudioBase = null;
      syncEngineBase = null;
      engine.open(engineUrl, { ...engineMeta, startAt: at });
    };
    let seekTimer = 0;
    const onSeeked = () => {
      clearTimeout(seekTimer);
      seekTimer = setTimeout(reopenCanvasAt, 300);
    };
    player.addEventListener('seeked', onSeeked);
    player.addEventListener('playing', () => { if (poster) poster.hidden = true; }, { once: true });
    currentEnginePlayer = player;
    currentEngineSeekHandler = onSeeked;
    currentEngineSyncTimer = setInterval(syncCanvas, 250);
    engine.on('state', (state) => {
      if (seq !== routeSeq || state.stage === 'idle') return;
      if (state.height > 0) updateQualityBadge(state.height, state.fps);
      if (state.stage === 'live') {
        if (status) status.hidden = true;
        if (poster) poster.hidden = true;
        const teslaBadge = $('#teslaBadge');
        if (teslaBadge) teslaBadge.hidden = false;
        updateMuteButton();
      }
    });
    engine.on('fail', (message) => {
      if (seq === routeSeq) showPlayerError(message || 'Tesla playback failed.', video);
    });
    engine.setClock(video.live ? null : syncClock);
    engine.open(engineUrl, engineMeta);
    engine.setVideoPaused(player.paused);
  }

  function setupPlayerControls(player, video) {
    const shell = player.closest('.player-shell');
    if (!shell) return;
    const controls = $('#playerControls');
    const playBtn = $('#playerPlay');
    const centerBtn = $('#playerCenter');
    const seek = $('#playerSeek');
    const currentEl = $('#playerCurrent');
    const durationEl = $('#playerDuration');
    const backBtn = $('#playerBack');
    const forwardBtn = $('#playerForward');
    const poster = $('#playerPoster');
    if (!controls || !playBtn || !centerBtn) return;

    let hideTimer = 0;
    let scrubbing = false;
    const alive = () => document.body.contains(player.element || player);
    const clearHide = () => {
      clearTimeout(hideTimer);
      hideTimer = 0;
    };
    const scheduleHide = () => {
      clearHide();
      if (player.paused || scrubbing) return;
      hideTimer = setTimeout(() => {
        if (alive() && !player.paused && !scrubbing) shell.classList.add('controls-hidden');
      }, 2800);
    };
    const showControls = (autoHide = true) => {
      shell.classList.remove('controls-hidden');
      if (autoHide) scheduleHide();
      else clearHide();
    };
    const setPlayState = () => {
      const paused = player.paused;
      playBtn.innerHTML = icon(paused ? 'play' : 'pause');
      playBtn.setAttribute('aria-label', paused ? 'Play' : 'Pause');
      shell.classList.toggle('is-paused', paused);
      shell.classList.toggle('is-playing', !paused);
    };
    const togglePlay = () => {
      showControls(false);
      if (player.paused) {
        if (player.ended) {
          try { player.currentTime = 0; } catch (e) {}
        }
        const started = player.play();
        if (started) started.catch(() => {
          setPlayState();
          showControls(false);
        });
      } else {
        player.pause();
      }
    };
    const bufferedEnd = (current) => {
      if (currentEngine && typeof currentEngine.state === 'function') {
        const state = currentEngine.state();
        if (state && state.stage !== 'idle' && Number.isFinite(state.buffered)) {
          return current + Math.max(0, state.buffered);
        }
      }
      let end = current;
      try {
        const ranges = player.buffered;
        for (let i = 0; i < ranges.length; i++) {
          const start = ranges.start(i);
          const rangeEnd = ranges.end(i);
          if (start <= current + 0.5 && rangeEnd >= current) {
            end = Math.max(end, rangeEnd);
          }
        }
      } catch (e) {}
      return end;
    };
    const updateBuffer = (current, duration) => {
      if (!seek) return;
      const playedPct = Number.isFinite(duration) && duration > 0
        ? Math.min(100, Math.max(0, (current / duration) * 100))
        : 0;
      const loadedPct = Number.isFinite(duration) && duration > 0
        ? Math.min(100, Math.max(0, (bufferedEnd(current) / duration) * 100))
        : playedPct;
      const pct = Math.min(100, Math.max(playedPct, loadedPct));
      seek.style.setProperty('--buffer', `${pct}%`);
    };
    const updateTime = () => {
      const duration = player.duration;
      const hasDuration = Number.isFinite(duration) && duration > 0;
      const current = Math.max(0, player.currentTime || 0);
      if (currentEl) currentEl.textContent = fmtDuration(current);
      if (durationEl) durationEl.textContent = hasDuration ? fmtDuration(duration) : '0:00';
      if (!seek) return;
      const pct = hasDuration ? Math.min(100, Math.max(0, (current / duration) * 100)) : 0;
      seek.disabled = !hasDuration;
      if (!scrubbing) {
        seek.value = String(Math.round(pct * 10));
        seek.style.setProperty('--seek', `${pct}%`);
      }
      updateBuffer(current, duration);
    };
    const beginScrub = () => {
      scrubbing = true;
      clearHide();
      showControls(false);
    };
    const endScrub = () => {
      if (!scrubbing) return;
      scrubbing = false;
      scheduleHide();
    };
    const skip = (delta) => {
      showControls();
      if (!Number.isFinite(player.duration) || player.duration <= 0) return;
      const next = Math.max(0, Math.min(player.duration, player.currentTime + delta));
      try {
        if (typeof player.seekTo === 'function') player.seekTo(next);
        else player.currentTime = next;
      } catch (e) {}
    };

    if (poster) {
      const sources = [
        `https://i.ytimg.com/vi/${video.id}/maxresdefault.jpg`,
        `https://i.ytimg.com/vi/${video.id}/hq720.jpg`,
        `https://i.ytimg.com/vi/${video.id}/mqdefault.jpg`
      ];
      let sourceIndex = 0;
      const fallbackPoster = () => {
        sourceIndex += 1;
        if (sourceIndex >= sources.length) {
          poster.style.display = 'none';
          return;
        }
        poster.src = sources[sourceIndex];
      };
      poster.addEventListener('error', fallbackPoster);
      poster.addEventListener('load', () => {
        if (sourceIndex < sources.length - 1 && poster.naturalWidth < 500) fallbackPoster();
      });
      player.addEventListener('playing', () => { poster.hidden = true; }, { once: true });
    }

    player.addEventListener('play', () => {
      setPlayState();
      showControls();
    });
    player.addEventListener('playing', () => {
      setPlayState();
      showControls();
    });
    player.addEventListener('pause', () => {
      setPlayState();
      showControls(false);
    });
    player.addEventListener('ended', () => {
      setPlayState();
      showControls(false);
    });
    player.addEventListener('timeupdate', updateTime);
    player.addEventListener('durationchange', updateTime);
    player.addEventListener('loadedmetadata', updateTime);
    player.addEventListener('click', () => {
      togglePlay();
    });
    playBtn.addEventListener('click', togglePlay);
    centerBtn.addEventListener('click', togglePlay);
    if (backBtn) backBtn.addEventListener('click', () => skip(-10));
    if (forwardBtn) forwardBtn.addEventListener('click', () => skip(10));
    shell.addEventListener('pointermove', () => showControls());
    shell.addEventListener('focusin', () => showControls(false));

    if (seek) {
      seek.addEventListener('pointerdown', beginScrub);
      seek.addEventListener('input', () => {
        if (!scrubbing) beginScrub();
        const duration = player.duration;
        if (!Number.isFinite(duration) || duration <= 0) return;
        const pct = Number(seek.value) / 10;
        seek.style.setProperty('--seek', `${pct}%`);
        updateBuffer((duration * pct) / 100, duration);
        if (currentEl) currentEl.textContent = fmtDuration((duration * pct) / 100);
        try { player.currentTime = (duration * pct) / 100; } catch (e) {}
      });
      seek.addEventListener('change', endScrub);
      seek.addEventListener('pointerup', endScrub);
      seek.addEventListener('pointercancel', endScrub);
      seek.addEventListener('keyup', endScrub);
      seek.addEventListener('blur', endScrub);
    }

    updateTime();
    setPlayState();
    const bufferTimer = setInterval(() => {
      if (!alive()) {
        clearInterval(bufferTimer);
        return;
      }
      updateTime();
    }, 750);
  }

  function startPlayer(video, startAt, seq) {
    currentVideo = video;
    const player = $('#playerVideo');
    const status = $('#playerStatus');
    if (!player) return;
    const useTeslaEngine = Boolean((video.hls || video.source) && teslaEnginePreferred());
    const teslaBadge = $('#teslaBadge');
    if (teslaBadge) {
      teslaBadge.hidden = false;
      teslaBadge.classList.toggle('engine', useTeslaEngine);
      teslaBadge.classList.toggle('standard', !useTeslaEngine);
      teslaBadge.dataset.defaultText = useTeslaEngine ? 'InMotion' : 'Standard video';
      teslaBadge.textContent = teslaBadge.dataset.defaultText;
      teslaBadge.title = (useTeslaEngine ? 'InMotion engine is active' : 'Native video player is active') +
        ' · Click to see the playback source';
    }
    if (useTeslaEngine) {
      if (window.TeslaPlayer) startTeslaEngine(video, startAt, seq);
      else showPlayerError('The Tesla canvas engine could not be loaded.', video);
      return;
    }
    setupPlayerControls(player, video);
    const revealPlayer = () => {
      if (seq === routeSeq && status) status.hidden = true;
    };
    player.addEventListener('playing', revealPlayer, { once: true });

    const preferDirect = Boolean(video.source) && isTeslaBrowser();
    if (preferDirect) {
      const qualityText = $('#qualityText');
      if (qualityText) qualityText.textContent = fmtQuality(video.directQuality?.height);
    }
    if (!video.hls || preferDirect) {
      if (!video.source) {
        showPlayerError('No playable stream was returned for this video.', video);
        return;
      }
      const directTitle = status && status.querySelector('.status-title');
      if (directTitle) directTitle.textContent = 'Buffering…';
      if (startAt > 0 && !video.live) {
        player.addEventListener('loadedmetadata', () => {
          try { player.currentTime = startAt; } catch (e) {}
        }, { once: true });
      }
      player.addEventListener('error', () => {
        if (seq === routeSeq) {
          showPlayerError('The stream could not be loaded. Try again in a moment.', video);
        }
      }, { once: true });
      player.src = video.source;
      const started = player.play();
      if (started) started.catch(() => {
        if (seq === routeSeq) revealPlayer();
      });
      return;
    }

    loadHls().then((Hls) => {
      if (seq !== routeSeq || !document.body.contains(player)) return;
      if (!Hls.isSupported()) {
        showPlayerError('This browser does not support the required player.', video);
        return;
      }
      const config = {
        enableWorker: true,
        capLevelToPlayerSize: true,
        backBufferLength: 30,
        maxBufferLength: video.live ? 20 : 30
      };
      if (video.live) {
        config.liveSyncDurationCount = 3;
        config.liveMaxLatencyDurationCount = 10;
      }
      const hls = new Hls(config);
      currentHls = hls;
      let recoveredMedia = false;

      hls.on(Hls.Events.MANIFEST_PARSED, () => {
        if (seq !== routeSeq) return;
        useOriginalAudio(hls, video);
        updateQualityFromLevels(hls);
        const statusTitle = status && status.querySelector('.status-title');
        if (statusTitle) statusTitle.textContent = video.live ? 'Joining live stream…' : 'Buffering…';
        if (startAt > 0 && !video.live) {
          const seek = () => {
            try { player.currentTime = startAt; } catch (e) {}
          };
          if (player.readyState >= 1) seek();
          else player.addEventListener('loadedmetadata', seek, { once: true });
        }
        const started = player.play();
        if (started) started.catch(() => {
          if (seq === routeSeq) revealPlayer();
        });
      });
      hls.on(Hls.Events.AUDIO_TRACKS_UPDATED, () => {
        if (seq === routeSeq) useOriginalAudio(hls, video);
      });
      hls.on(Hls.Events.AUDIO_TRACK_SWITCHED, () => {
        if (seq === routeSeq) useOriginalAudio(hls, video);
      });

      hls.on(Hls.Events.ERROR, (event, data) => {
        if (seq !== routeSeq || !data.fatal) return;
        if (data.type === Hls.ErrorTypes.MEDIA_ERROR && !recoveredMedia) {
          recoveredMedia = true;
          hls.recoverMediaError();
          return;
        }
        showPlayerError('The stream could not be loaded. It may have ended or the public server may be busy.', video);
      });

      hls.loadSource(video.hls);
      hls.attachMedia(player);
    }).catch(() => {
      if (seq === routeSeq) showPlayerError('The video player could not be loaded.', video);
    });
  }

  function readWatchCache(id) {
    try {
      const raw = localStorage.getItem(`youtube:watch:${id}`);
      if (!raw) return null;
      const saved = JSON.parse(raw);
      if (!saved || !saved.video || !saved.video.id) return null;
      const ttl = saved.video.live ? 30000 : 300000;
      if (Date.now() - Number(saved.at || 0) > ttl) return null;
      if ((!saved.video.streamSource || saved.video.streamSource === 'public') && lastSource) {
        saved.video.streamSource = lastSource.type;
        saved.video.streamOrigin = sourceHost(lastSource.base);
      }
      return saved.video;
    } catch (e) {
      return null;
    }
  }

  function writeWatchCache(video) {
    try {
      const clipped = { ...video, related: (video.related || []).slice(0, 12) };
      localStorage.setItem(`youtube:watch:${video.id}`, JSON.stringify({ at: Date.now(), video: clipped }));
      const prefix = 'youtube:watch:';
      const entries = [];
      for (let i = 0; i < localStorage.length; i += 1) {
        const key = localStorage.key(i);
        if (!key || !key.startsWith(prefix)) continue;
        let at = 0;
        try { at = Number(JSON.parse(localStorage.getItem(key)).at) || 0; } catch (e) {}
        entries.push({ key, at });
      }
      entries.sort((a, b) => b.at - a.at);
      entries.slice(8).forEach((entry) => localStorage.removeItem(entry.key));
    } catch (e) {}
  }

  async function watchView(id, seq, signal) {
    view.innerHTML = watchSkeletonHTML();
    document.title = 'Loading - YouTube';
    preloadTeslaLibs().catch(() => null);
    loadHls().catch(() => null);
    const hlsReady = Promise.resolve(null);
    let video = null;
    let pageReady = false;
    let loadFailed = false;
    const renderPage = (candidate) => {
      if (!candidate || loadFailed || pageReady || seq !== routeSeq || signal.aborted) return false;
      pageReady = true;
      view.innerHTML = watchHTML(candidate);
      document.title = `${candidate.title} - YouTube`;
      wireWatch(candidate);
      return true;
    };
    const cached = readWatchCache(id);
    if (cached && renderPage(cached)) {
      const canUseCached = yatteeOnly()
        ? cached.streamSource === 'yattee'
        : !yatteeEnabled() || cached.streamSource === 'yattee' || cached.live;
      if (canUseCached) {
        const cachedStart = parseStart(new URLSearchParams(location.search).get('t'));
        startPlayer(cached, cachedStart, seq);
        return;
      }
    }
    try {
      video = await loadStream(id, signal, renderPage);
    } catch (e) {
      if (signal.aborted) return;
      loadFailed = true;
    }
    await hlsReady;
    if (seq !== routeSeq || signal.aborted) return;
    if (!video) {
      loadFailed = true;
      document.title = 'Video unavailable - YouTube';
      view.innerHTML = watchErrorHTML(id);
      return;
    }
    writeWatchCache(video);
    if (!pageReady) renderPage(video);
    else document.title = `${video.title} - YouTube`;
    const start = parseStart(new URLSearchParams(location.search).get('t'));
    startPlayer(video, start, seq);
  }

  function setTheme(theme) {
    document.documentElement.dataset.theme = theme;
    const dark = theme === 'dark';
    themeColor.setAttribute('content', dark ? '#0f0f0f' : '#ffffff');
    themeBtn.setAttribute('aria-label', dark ? 'Switch to light theme' : 'Switch to dark theme');
    try { localStorage.setItem('dltube-theme', theme); } catch (e) {}
  }

  function navigate(href) {
    let target;
    try {
      target = new URL(href, location.href);
    } catch (e) {
      return;
    }
    if (target.pathname === location.pathname && target.search === location.search) {
      window.scrollTo(0, 0);
      route();
      return;
    }
    history.pushState(null, '', href);
    closeGuide();
    window.scrollTo(0, 0);
    route();
  }

  function normalizePlaylistVideo(item, base) {
    const thumb = (item.authorThumbnails || []).slice(-1)[0];
    return {
      id: item.videoId,
      title: item.title || 'Untitled',
      channel: item.author || 'Unknown',
      uploaderUrl: item.authorUrl || '',
      avatar: thumb ? absoluteURL(thumb.url, base) : '',
      views: -1,
      duration: Number(item.lengthSeconds || 0),
      live: item.liveNow === true,
      when: '',
      description: ''
    };
  }

  async function fetchPlaylist(id, signal) {
    const attempts = [];
    const pipedBases = [...APIS, ...PIPED_FALLBACK.slice(0, 8)];
    const invidiousBases = [...INVIDIOUS_FALLBACK, ...(instanceCache.invidious || []).slice(0, 6)];
    for (const base of pipedBases) {
      attempts.push(
        apiFetch(base, `/playlists/${encodeURIComponent(id)}?_=${Date.now()}`, signal).then((data) => {
          const videos = (data.relatedStreams || [])
            .map(normalizeItem)
            .filter((video) => video && video.id);
          if (!videos.length) throw new Error('No videos');
          return { name: data.name || 'Playlist', videos };
        })
      );
    }
    if (yatteeEnabled()) {
      attempts.push(
        sleepMs(850).then(() => fetchYatteePlaylist(id, signal))
      );
    }
    for (const base of invidiousBases) {
      attempts.push(
        fetch(`${base}/api/v1/playlists/${encodeURIComponent(id)}?_=${Date.now()}`, {
          signal,
          cache: 'no-store',
          headers: { Accept: 'application/json' }
        })
          .then((response) => {
            if (!response.ok) throw new Error('Unexpected response');
            return response.json();
          })
          .then((data) => {
            const videos = (data.videos || [])
              .map((item) => normalizePlaylistVideo(item, base))
              .filter((video) => video && video.id);
            if (!videos.length) throw new Error('No videos');
            return { name: data.title || 'Playlist', videos };
          })
      );
    }
    return new Promise((resolve, reject) => {
      let best = null;
      let settled = 0;
      let finished = false;
      let timer = 0;
      const finish = () => {
        if (finished) return;
        finished = true;
        clearTimeout(timer);
        if (best) resolve(best);
        else reject(new Error('No playlist'));
      };
      const consider = (data) => {
        if (!best || data.videos.length > best.videos.length) best = data;
        if (!timer) timer = setTimeout(finish, 900);
      };
      for (const attempt of attempts) {
        attempt
          .then(consider)
          .catch(() => {})
          .finally(() => {
            settled += 1;
            if (settled === attempts.length) finish();
          });
      }
    });
  }

  async function playlistView(id, seq, signal) {
    view.innerHTML = `<div class="results-page">
      <h1 class="search-heading">Loading playlist…</h1>
      ${skeletonGrid()}
    </div>`;
    try {
      const data = await fetchPlaylist(id, signal);
      if (seq !== routeSeq || signal.aborted) return;
      document.title = `${data.name} - YouTube`;
      if (!data.videos.length) {
        view.innerHTML = `<div class="results-page">
          <h1 class="search-heading">${esc(data.name)}</h1>
          ${stateHTML('No videos', 'This playlist has no videos to show.')}
        </div>`;
        return;
      }
      view.innerHTML = `<div class="results-page">
        <h1 class="search-heading">${esc(data.name)}</h1>
        <div class="desc-meta">${data.videos.length} video${data.videos.length === 1 ? '' : 's'}</div>
        <div class="grid">${data.videos.map(cardHTML).join('')}</div>
      </div>`;
    } catch (e) {
      if (seq !== routeSeq || signal.aborted) return;
      document.title = 'Playlist - YouTube';
      view.innerHTML = `<div class="results-page">
        <h1 class="search-heading">Playlist</h1>
        ${errorStateHTML('Playlist unavailable', 'The public video servers did not respond. Please try again.')}
      </div>`;
    }
  }

  const SAVED_KEY = 'youtube:saved';

  function loadSaved() {
    try {
      const list = JSON.parse(localStorage.getItem(SAVED_KEY) || '[]');
      return Array.isArray(list) ? list.filter((item) => item && item.id) : [];
    } catch (e) {
      return [];
    }
  }

  function writeSaved(list) {
    try { localStorage.setItem(SAVED_KEY, JSON.stringify(list)); } catch (e) {}
  }

  function isSaved(id) {
    return loadSaved().some((item) => item.id === id);
  }

  function addSaved(video) {
    const list = loadSaved().filter((item) => item.id !== video.id);
    list.unshift({
      id: video.id,
      title: video.title,
      channel: video.channel,
      avatar: video.avatar || '',
      uploaderUrl: video.uploaderUrl || '',
      views: video.views,
      duration: video.duration,
      live: video.live === true,
      when: video.when || '',
      description: video.description || ''
    });
    writeSaved(list);
  }

  function removeSaved(id) {
    writeSaved(loadSaved().filter((item) => item.id !== id));
  }

  let modalOpenedAt = 0;
  function closeModal() {
    const modal = $('#modal');
    if (modal) modal.hidden = true;
  }

  function openConfirm(title, text, confirmLabel, onConfirm) {
    const modal = $('#modal');
    if (!modal) return;
    modalOpenedAt = Date.now();
    $('#modalTitle').textContent = title;
    $('#modalText').textContent = text;
    const confirmBtn = $('#modalConfirm');
    confirmBtn.textContent = confirmLabel;
    confirmBtn.onclick = () => {
      closeModal();
      onConfirm();
    };
    modal.hidden = false;
  }

  let toastTimer = 0;
  function showToast(message) {
    const el = $('#toast');
    if (!el) return;
    clearTimeout(toastTimer);
    el.textContent = message;
    el.classList.add('show');
    toastTimer = setTimeout(() => el.classList.remove('show'), 1800);
  }

  function handleThumbLongPress(thumb) {
    const link = thumb.closest('a[data-nav]');
    if (!link) return;
    let id = '';
    try {
      const url = new URL(link.getAttribute('href'), location.href);
      id = extractVideoId(url.searchParams.get('v') || '');
    } catch (e) {}
    if (!id) return;
    const video = videoCache.get(id) || loadSaved().find((item) => item.id === id);
    if (!video) return;
    if (isSaved(id)) {
      openConfirm(
        'Remove from Saved?',
        `Remove "${video.title}" from your Saved list?`,
        'Remove',
        () => {
          removeSaved(id);
          showToast('Removed from Saved');
          if (new URLSearchParams(location.search).has('saved')) savedView();
        }
      );
    } else {
      addSaved(video);
      showToast('Added to Saved');
    }
  }

  function savedView() {
    const saved = loadSaved();
    document.title = 'Saved - YouTube';
    if (!saved.length) {
      view.innerHTML = `<div class="results-page">
        <h1 class="search-heading">Saved</h1>
        ${stateHTML('No saved videos', 'Use the Save button on a video to add it here.')}
      </div>`;
      return;
    }
    view.innerHTML = `<div class="results-page">
      <h1 class="search-heading">Saved</h1>
      <div class="desc-meta">${saved.length} video${saved.length === 1 ? '' : 's'}</div>
      <div class="grid">${saved.map(cardHTML).join('')}</div>
    </div>`;
  }

  function yatteeChannelVideo(item, author, avatar) {
    if (!item || !item.videoId) return null;
    return {
      id: item.videoId,
      title: item.title || 'Untitled',
      channel: author,
      uploaderUrl: item.authorId ? `/channel/${item.authorId}` : '',
      avatar,
      views: Number(item.viewCount ?? -1),
      duration: Number(item.lengthSeconds || 0),
      live: item.liveNow === true,
      when: item.publishedText || '',
      description: plainText(item.description || '')
    };
  }

  async function fetchYatteeChannel(id, signal) {
    const base = yatteeApiBase();
    if (!base) throw new Error('Yattee unavailable');
    const channelPath = `/api/v1/channels/${encodeURIComponent(id)}`;
    const [meta, videosData, streamsData] = await Promise.all([
      yatteeApiFetch(channelPath, signal),
      yatteeApiFetch(`${channelPath}/videos`, signal).catch(() => ({ videos: [] })),
      yatteeApiFetch(`${channelPath}/streams`, signal).catch(() => ({ videos: [] }))
    ]);
    if (!meta || !meta.author) throw new Error('Channel unavailable');
    const thumb = (meta.authorThumbnails || []).slice(-1)[0];
    const avatar = thumb ? absoluteURL(thumb.url, base) : '';
    const seen = new Set();
    const videos = [];
    for (const item of [...(streamsData.videos || []), ...(videosData.videos || [])]) {
      const video = yatteeChannelVideo(item, meta.author, avatar);
      if (!video || seen.has(video.id)) continue;
      seen.add(video.id);
      videos.push(video);
    }
    if (!videos.length) throw new Error('No videos');
    return {
      name: meta.author,
      avatar,
      subscribers: Number(meta.subCount ?? -1),
      description: plainText(meta.description || ''),
      videos: videos.slice(0, 30),
      tabs: [],
      base
    };
  }

  async function fetchYatteePlaylist(id, signal) {
    const base = yatteeApiBase();
    if (!base) throw new Error('Yattee unavailable');
    const data = await yatteeApiFetch(`/api/v1/playlists/${encodeURIComponent(id)}`, signal);
    const videos = (data.videos || [])
      .map((item) => normalizePlaylistVideo(item, base))
      .filter((video) => video && video.id);
    if (!videos.length) throw new Error('No videos');
    const channelIDs = [...new Set(videos
      .map((video) => channelIDFromURL(video.uploaderUrl))
      .filter(Boolean))].slice(0, 8);
    await Promise.all(channelIDs.map(async (channelID) => {
      try {
        const meta = await yatteeApiFetch(`/api/v1/channels/${encodeURIComponent(channelID)}`, signal);
        const thumb = (meta.authorThumbnails || []).slice(-1)[0];
        if (!thumb) return;
        const avatar = absoluteURL(thumb.url, base);
        for (const video of videos) {
          if (channelIDFromURL(video.uploaderUrl) === channelID) video.avatar = avatar;
        }
      } catch (e) {}
    }));
    return { name: data.title || 'Playlist', videos };
  }

  async function fetchChannel(id, signal) {
    const pipedAttempts = APIS.map(async (base) => {
      const data = await apiFetch(base, `/channel/${encodeURIComponent(id)}`, signal);
      if (!data || !data.name) throw new Error('Channel unavailable');
      const avatar = data.avatarUrl || '';
      const videos = (data.relatedStreams || [])
        .map(normalizeItem)
        .filter((video) => video && video.id)
        .map((video) => {
          if (!video.avatar) video.avatar = avatar;
          return video;
        });
      if (!videos.length) throw new Error('No videos');
      return {
        name: data.name,
        avatar,
        subscribers: Number(data.subscriberCount ?? -1),
        description: plainText(data.description || ''),
        videos,
        tabs: data.tabs || [],
        base
      };
    });
    const pipedPromise = Promise.any(pipedAttempts);
    try {
      if (yatteeEnabled()) {
        return await Promise.any([
          pipedPromise,
          sleepMs(850).then(() => fetchYatteeChannel(id, signal))
        ]);
      }
      return await pipedPromise;
    } catch (e) {}

    const invidiousAttempts = INVIDIOUS_FALLBACK.map(async (base) => {
      const controller = new AbortController();
      const abort = () => controller.abort();
      if (signal) signal.addEventListener('abort', abort, { once: true });
      const timer = setTimeout(() => controller.abort(), 8000);
      try {
        const response = await fetch(`${base}/api/v1/channels/${encodeURIComponent(id)}`, {
          signal: controller.signal,
          cache: 'no-store',
          headers: { Accept: 'application/json' }
        });
        if (!response.ok) throw new Error('Channel unavailable');
        const data = await response.json();
        const author = data.author || 'Channel';
        const avatar = (data.authorThumbnails || []).slice(-1)[0];
        const avatarURL = avatar ? absoluteURL(avatar.url, base) : '';
        const list = data.latestVideos || data.videos || [];
        const videos = list.map((item) => ({
          id: item.videoId,
          title: item.title || 'Untitled',
          channel: author,
          uploaderUrl: '',
          avatar: avatarURL,
          views: Number(item.viewCount ?? -1),
          duration: Number(item.lengthSeconds ?? 0),
          live: item.liveNow === true,
          when: item.publishedText || '',
          description: ''
        })).filter((video) => video.id);
        if (!videos.length) throw new Error('No videos');
        return {
          name: author,
          avatar: avatarURL,
          subscribers: Number(data.subCount ?? -1),
          description: plainText(data.description || ''),
          videos,
          tabs: [],
          base: null
        };
      } finally {
        clearTimeout(timer);
        if (signal) signal.removeEventListener('abort', abort);
      }
    });
    try {
      return await Promise.any(invidiousAttempts);
    } catch (e) {
      return null;
    }
  }

  async function fetchChannelLive(tabData, signal) {
    const attempts = APIS.map(async (base) => {
      const response = await fetch(`${base}/channels/tabs?data=${encodeURIComponent(tabData)}`, {
        signal,
        cache: 'no-store',
        headers: { Accept: 'application/json' }
      });
      if (!response.ok) throw new Error('Tab unavailable');
      const data = await response.json();
      const items = (data.content || [])
        .map(normalizeItem)
        .filter((video) => video && video.id);
      if (!items.length) throw new Error('No live videos');
      return items;
    });
    try {
      return await Promise.any(attempts);
    } catch (e) {
      return [];
    }
  }

  async function channelView(id, seq, signal) {
    view.innerHTML = `<div class="results-page"><h1 class="search-heading">Loading channel…</h1>${skeletonGrid()}</div>`;
    try {
      const data = await fetchChannel(id, signal);
      if (seq !== routeSeq || signal.aborted) return;
      if (!data) {
        document.title = 'Channel - YouTube';
        view.innerHTML = `<div class="results-page"><h1 class="search-heading">Channel</h1>${errorStateHTML('Channel unavailable', 'The public video servers did not respond. Please try again.')}</div>`;
        return;
      }
      document.title = `${data.name} - YouTube`;
      const subs = data.subscribers >= 0 ? `${fmtCount(data.subscribers)} subscribers` : 'Channel';
      const description = data.description
        ? `<p class="channel-desc">${esc(data.description.slice(0, 400))}</p>`
        : '';
      const paint = (videos) => {
        const sorted = [...videos].sort((a, b) => Number(b.live) - Number(a.live));
        view.innerHTML = `<div class="results-page">
          <div class="channel-head">
            ${avatarHTML(data.name, data.avatar)}
            <div class="channel-info">
              <h1 class="search-heading">${esc(data.name)}</h1>
              <div class="desc-meta">${esc(subs)} • ${sorted.length} video${sorted.length === 1 ? '' : 's'}</div>
              ${description}
            </div>
          </div>
          <h2 class="section-heading">Videos &amp; live</h2>
          ${sorted.length ? `<div class="grid">${sorted.map(cardHTML).join('')}</div>` : stateHTML('No videos', 'This channel has no public videos to show.')}
        </div>`;
      };
      paint(data.videos);

      const liveTab = (data.tabs || []).find((tab) => tab.name === 'livestreams');
      if (liveTab && liveTab.data) {
        fetchChannelLive(liveTab.data, signal).then((liveVideos) => {
          if (seq !== routeSeq || signal.aborted || !liveVideos.length) return;
          for (const video of liveVideos) {
            if (!video.avatar) video.avatar = data.avatar;
          }
          const seen = new Set();
          const merged = [];
          for (const video of [...liveVideos, ...data.videos]) {
            if (!seen.has(video.id)) {
              seen.add(video.id);
              merged.push(video);
            }
          }
          paint(merged);
        }).catch(() => {});
      }
    } catch (e) {
      if (seq !== routeSeq || signal.aborted) return;
      document.title = 'Channel - YouTube';
      view.innerHTML = `<div class="results-page"><h1 class="search-heading">Channel</h1>${errorStateHTML('Channel unavailable', 'The public video servers did not respond. Please try again.')}</div>`;
    }
  }

  function settingsView() {
    const config = yatteeConfig();
    const limit = maxDefinition();
    document.title = 'Settings - YouTube';
    view.innerHTML = `<div class="results-page settings-page">
      <h1 class="search-heading">Settings</h1>

      <section class="settings-section">
        <h2>Playback</h2>
        <label class="settings-check" for="allow1080">
          <input type="checkbox" id="allow1080"${limit > 720 ? ' checked' : ''}>
          <span>
            <strong>Allow 1080p resolution when available</strong>
            <small>720p is the default to save bandwidth and data.</small>
          </span>
        </label>
        <label class="settings-check" for="yatteeOnly">
          <input type="checkbox" id="yatteeOnly"${yatteeOnly() ? ' checked' : ''}>
          <span>
            <strong>Force Yattee server only as video source</strong>
            <small>Disables public-source playback and fallback. Live streams may take longer to start.</small>
          </span>
        </label>
      </section>

      <section class="settings-section">
        <h2>Yattee server</h2>
        <p class="settings-help">Preferred source for on-demand videos. Live streams use the public source so they start immediately, unless forced above.</p>
        <label class="settings-field" for="yatteeUrl">
          <span>Server URL</span>
          <input type="url" id="yatteeUrl" value="${esc(config.url)}" placeholder="${DEFAULT_YATTEE_URL}" spellcheck="false" autocapitalize="off">
        </label>
        <label class="settings-field" for="yatteeUser">
          <span>Username</span>
          <input type="text" id="yatteeUser" value="${esc(config.user)}" placeholder="${DEFAULT_YATTEE_USER}" autocomplete="username" spellcheck="false" autocapitalize="off">
        </label>
        <label class="settings-field" for="yatteePassword">
          <span>Password</span>
          <input type="password" id="yatteePassword" value="" autocomplete="current-password" placeholder="${config.password ? 'Password saved — leave blank to keep' : 'Enter password'}">
        </label>
        <div class="settings-actions">
          <button type="button" class="btn settings-save" id="saveYatteeSettings">Save</button>
          <button type="button" class="btn settings-clear" id="clearYatteeSettings">Clear</button>
        </div>
        <div class="settings-status" id="settingsStatus" role="status"></div>
        <p class="settings-help settings-privacy">Credentials are stored only in this browser. Use a regular Yattee user, not an admin account. Leave the password blank and save to keep the current one.</p>
      </section>
    </div>`;

    const status = $('#settingsStatus');
    const urlField = $('#yatteeUrl');
    const userField = $('#yatteeUser');
    const passField = $('#yatteePassword');

    const setStatus = (message, error = false) => {
      status.textContent = message;
      status.classList.toggle('error', error);
    };

    $('#allow1080').addEventListener('change', (event) => {
      try {
        if (event.target.checked) localStorage.setItem('youtube:allow-1080', '1');
        else localStorage.removeItem('youtube:allow-1080');
        localStorage.removeItem('youtube:max-height');
      } catch (e) {}
      clearWatchCache();
    });

    $('#yatteeOnly').addEventListener('change', (event) => {
      try {
        if (event.target.checked) localStorage.setItem('youtube:yattee-only', '1');
        else localStorage.removeItem('youtube:yattee-only');
      } catch (e) {}
      clearWatchCache();
    });

    $('#saveYatteeSettings').addEventListener('click', () => {
      let url = urlField.value.trim().replace(/\/+$/, '');
      if (url) {
        try {
          const parsed = new URL(url);
          if (!/^https?:$/.test(parsed.protocol)) throw new Error('Bad protocol');
        } catch (e) {
          setStatus('Enter a valid http or https server URL.', true);
          return;
        }
      }
      const previous = yatteeConfig();
      const password = passField.value || previous.password || '';
      const next = { url, user: userField.value.trim(), password };
      if (!saveYatteeConfig(next)) {
        setStatus('Could not save settings in this browser.', true);
        return;
      }
      clearWatchCache();
      passField.value = '';
      passField.placeholder = password ? 'Password saved — leave blank to keep' : 'Enter password';
      setStatus(password && next.url
        ? 'Saved. Yattee will be tried first for videos.'
        : password
          ? 'Saved. Add a server URL to enable Yattee.'
          : 'Saved. Yattee stays disabled until a password is entered.');
    });

    $('#clearYatteeSettings').addEventListener('click', () => {
      try { localStorage.removeItem('youtube:yattee'); } catch (e) {}
      clearWatchCache();
      urlField.value = DEFAULT_YATTEE_URL;
      userField.value = DEFAULT_YATTEE_USER;
      passField.value = '';
      passField.placeholder = 'Enter password';
      setStatus('Yattee settings cleared. Videos will use the public servers.');
    });
  }

  async function route() {
    const seq = ++routeSeq;
    const teslaBadge = $('#teslaBadge');
    if (teslaBadge) teslaBadge.hidden = true;
    if (routeAbort) routeAbort.abort();
    routeAbort = new AbortController();
    const signal = routeAbort.signal;
    if (currentHls) {
      try { currentHls.destroy(); } catch (e) {}
      currentHls = null;
    }
    currentVideo = null;
    if (currentEngine) {
      try { currentEngine.destroy(); } catch (e) {}
      currentEngine = null;
    }
    if (currentEngineSyncTimer) clearInterval(currentEngineSyncTimer);
    currentEngineSyncTimer = 0;
    if (currentEnginePlayer && currentEngineSeekHandler) {
      currentEnginePlayer.removeEventListener('seeked', currentEngineSeekHandler);
    }
    currentEnginePlayer = null;
    currentEngineSeekHandler = null;
    hideSuggestions();
    closeGuide();

    const params = new URLSearchParams(location.search);
    const id = extractVideoId(params.get('v') || '');
    const list = (params.get('list') || '').trim();
    const channel = (params.get('channel') || '').trim();
    const query = (params.get('q') || '').trim();

    if (id) {
      document.body.classList.add('watch');
      updateNav('watch');
      searchInput.value = '';
      await watchView(id, seq, signal);
    } else if (params.has('settings')) {
      document.body.classList.remove('watch');
      updateNav('settings');
      searchInput.value = '';
      settingsView();
    } else if (params.has('saved')) {
      document.body.classList.remove('watch');
      updateNav('saved');
      searchInput.value = '';
      savedView();
    } else if (channel && /^(?:@[A-Za-z0-9._-]+|[A-Za-z0-9_-]{10,})$/.test(channel)) {
      document.body.classList.remove('watch');
      updateNav('channel');
      searchInput.value = '';
      await channelView(channel, seq, signal);
    } else if (list && /^[A-Za-z0-9_-]{10,}$/.test(list)) {
      document.body.classList.remove('watch');
      updateNav('playlist', list);
      searchInput.value = '';
      await playlistView(list, seq, signal);
    } else {
      document.body.classList.remove('watch');
      if (query) {
        updateNav('search', query);
        await searchView(query, seq, signal);
      } else {
        updateNav('home');
        searchInput.value = '';
        await homeView(seq, signal);
      }
    }
  }

  const suggestionCache = new Map();
  let suggestionController = null;
  let suggestionTimer = 0;
  let suggestionItems = [];
  let activeSuggestion = -1;

  function hideSuggestions() {
    clearTimeout(suggestionTimer);
    suggestionTimer = 0;
    if (suggestionController) {
      suggestionController.abort();
      suggestionController = null;
    }
    suggestionItems = [];
    activeSuggestion = -1;
    searchSuggestions.hidden = true;
    searchSuggestions.innerHTML = '';
    searchInput.setAttribute('aria-expanded', 'false');
  }

  function paintSuggestions(items) {
    suggestionItems = items;
    activeSuggestion = -1;
    searchSuggestions.innerHTML = items.map((item, index) => `
      <button class="search-suggestion" type="button" role="option" aria-selected="false" data-suggestion-index="${index}">
        ${icon('search')}<span>${esc(item)}</span>
      </button>`).join('');
    searchSuggestions.hidden = false;
    searchInput.setAttribute('aria-expanded', 'true');
  }

  function setActiveSuggestion(index) {
    if (!suggestionItems.length) return;
    activeSuggestion = (index + suggestionItems.length) % suggestionItems.length;
    [...searchSuggestions.children].forEach((item, itemIndex) => {
      const active = itemIndex === activeSuggestion;
      item.classList.toggle('active', active);
      item.setAttribute('aria-selected', String(active));
      if (active) item.scrollIntoView({ block: 'nearest' });
    });
  }

  function chooseSuggestion(value) {
    searchInput.value = value;
    hideSuggestions();
    searchForm.requestSubmit();
  }

  async function fetchSuggestions(query, signal) {
    const cached = suggestionCache.get(query);
    if (cached && Date.now() - cached.at < 120000) return cached.items;
    const cleanList = (data) => {
      const list = Array.isArray(data)
        ? data
        : data && Array.isArray(data.suggestions) ? data.suggestions : [];
      return [...new Set(list
        .filter((item) => typeof item === 'string' && item.trim())
        .map((item) => item.trim()))].slice(0, 8);
    };
    const attempts = APIS.map(async (base) => {
      const response = await fetch(
        `${base}/suggestions?query=${encodeURIComponent(query)}`,
        {
          signal,
          cache: 'no-store',
          priority: 'high',
          headers: { Accept: 'application/json' }
        }
      );
      if (!response.ok) throw new Error('Suggestions unavailable');
      const clean = cleanList(await response.json());
      if (!clean.length) throw new Error('No suggestions');
      return clean;
    });
    const publicPromise = Promise.any(attempts);
    let items;
    if (yatteeEnabled()) {
      items = await new Promise((resolve, reject) => {
        let done = false;
        let primaryFailed = false;
        let primaryError = null;
        let fallbackStarted = false;
        let timer = 0;
        const finish = (value) => {
          if (done) return;
          done = true;
          clearTimeout(timer);
          resolve(value);
        };
        const fallback = () => {
          if (done || fallbackStarted) return;
          fallbackStarted = true;
          yatteeApiFetch(`/api/v1/search/suggestions?q=${encodeURIComponent(query)}`, signal).then((data) => {
            const clean = cleanList(data);
            if (!clean.length) throw new Error('No suggestions');
            finish(clean);
          }).catch((e) => {
            if (primaryFailed && !done) {
              done = true;
              clearTimeout(timer);
              reject(primaryError || e);
            }
          });
        };
        timer = setTimeout(fallback, 850);
        publicPromise.then(finish, (e) => {
          primaryFailed = true;
          primaryError = e;
          clearTimeout(timer);
          fallback();
        });
      });
    } else {
      items = await publicPromise;
    }
    suggestionCache.set(query, { at: Date.now(), items });
    if (suggestionCache.size > 30) {
      suggestionCache.delete(suggestionCache.keys().next().value);
    }
    return items;
  }

  function requestSuggestions() {
    hideSuggestions();
    const query = searchInput.value.trim();
    if (query.length < 2) return;
    suggestionTimer = setTimeout(async () => {
      const controller = new AbortController();
      suggestionController = controller;
      try {
        const items = await fetchSuggestions(query, controller.signal);
        if (controller.signal.aborted || searchInput.value.trim() !== query) return;
        paintSuggestions(items);
      } catch (e) {
        if (!controller.signal.aborted) hideSuggestions();
      }
    }, 140);
  }

  searchInput.addEventListener('input', requestSuggestions);
  searchInput.addEventListener('blur', () => {
    setTimeout(() => {
      if (!searchSuggestions.contains(document.activeElement)) hideSuggestions();
    }, 120);
  });
  searchInput.addEventListener('keydown', (event) => {
    if (searchSuggestions.hidden || !suggestionItems.length) {
      if (event.key === 'Escape') hideSuggestions();
      return;
    }
    if (event.key === 'ArrowDown') {
      event.preventDefault();
      setActiveSuggestion(activeSuggestion + 1);
    } else if (event.key === 'ArrowUp') {
      event.preventDefault();
      setActiveSuggestion(activeSuggestion - 1);
    } else if (event.key === 'Enter' && activeSuggestion >= 0) {
      event.preventDefault();
      chooseSuggestion(suggestionItems[activeSuggestion]);
    } else if (event.key === 'Escape') {
      event.preventDefault();
      hideSuggestions();
    }
  });
  searchSuggestions.addEventListener('mousedown', (event) => event.preventDefault());
  searchSuggestions.addEventListener('click', (event) => {
    const item = event.target.closest('[data-suggestion-index]');
    if (!item) return;
    const index = Number(item.dataset.suggestionIndex);
    if (Number.isInteger(index) && suggestionItems[index]) chooseSuggestion(suggestionItems[index]);
  });

  searchForm.addEventListener('submit', (event) => {
    event.preventDefault();
    hideSuggestions();
    event.preventDefault();
    const value = searchInput.value.trim();
    if (!value) return;
    const id = extractVideoId(value);
    if (id) {
      let start = '';
      try {
        const url = new URL(value, location.href);
        const time = url.searchParams.get('t') || url.searchParams.get('start');
        if (time) start = `&t=${encodeURIComponent(time)}`;
      } catch (e) {}
      navigate(`?v=${id}${start}`);
      return;
    }
    navigate(`?q=${encodeURIComponent(value)}`);
  });

  menuBtn.addEventListener('click', () => {
    if (matchMedia('(max-width: 1000px)').matches) {
      document.body.classList.toggle('guide-open');
      return;
    }
    const closed = document.body.classList.toggle('guide-closed');
    try { localStorage.setItem('dltube-guide', closed ? 'closed' : 'open'); } catch (e) {}
  });

  scrim.addEventListener('click', closeGuide);
  $('#modalCancel')?.addEventListener('click', closeModal);
  $('#modal')?.addEventListener('click', (event) => {
    if (event.target === event.currentTarget && Date.now() - modalOpenedAt > 500) closeModal();
  });
  document.addEventListener('keydown', (event) => {
    if (event.key === 'Escape') closeModal();
  });

  let thumbPressTimer = 0;
  let thumbPressStart = null;
  let thumbPressPending = null;
  let suppressThumbClick = false;
  const cancelThumbPress = () => {
    clearTimeout(thumbPressTimer);
    thumbPressTimer = 0;
    thumbPressStart = null;
    thumbPressPending = null;
  };
  const finishThumbPress = () => {
    clearTimeout(thumbPressTimer);
    thumbPressTimer = 0;
    thumbPressStart = null;
    const pending = thumbPressPending;
    thumbPressPending = null;
    if (pending) setTimeout(() => handleThumbLongPress(pending), 0);
  };
  view.addEventListener('pointerdown', (event) => {
    if (event.pointerType === 'mouse' && event.button !== 0) return;
    const thumb = event.target.closest('.thumb');
    if (!thumb || !thumb.closest('a[data-nav]')) return;
    thumbPressStart = { x: event.clientX, y: event.clientY, thumb };
    thumbPressPending = null;
    clearTimeout(thumbPressTimer);
    thumbPressTimer = setTimeout(() => {
      thumbPressTimer = 0;
      const start = thumbPressStart;
      if (!start) return;
      thumbPressPending = start.thumb;
      suppressThumbClick = true;
      setTimeout(() => { suppressThumbClick = false; }, 1200);
    }, 550);
  });
  view.addEventListener('pointermove', (event) => {
    if (!thumbPressStart) return;
    const dx = event.clientX - thumbPressStart.x;
    const dy = event.clientY - thumbPressStart.y;
    if (Math.hypot(dx, dy) > 12) cancelThumbPress();
  });
  view.addEventListener('pointerup', finishThumbPress);
  view.addEventListener('pointercancel', cancelThumbPress);
  view.addEventListener('pointerleave', cancelThumbPress);
  view.addEventListener('contextmenu', (event) => {
    if (event.target.closest('.thumb')) event.preventDefault();
  });
  view.addEventListener('click', (event) => {
    if (!suppressThumbClick) return;
    suppressThumbClick = false;
    event.preventDefault();
    event.stopPropagation();
  }, true);

  document.addEventListener('error', (event) => {
    const image = event.target;
    if (!(image instanceof HTMLImageElement) || !image.classList.contains('avatar-img')) return;
    if (image.dataset.fallback) {
      const fallback = image.dataset.fallback;
      delete image.dataset.fallback;
      image.src = fallback;
      return;
    }
    image.remove();
  }, true);

  document.addEventListener('keydown', (event) => {
    if (event.key === 'Escape') closeGuide();
  });

  document.addEventListener('click', (event) => {
    const retry = event.target.closest('[data-retry]');
    if (retry) {
      event.preventDefault();
      route();
      return;
    }
    const link = event.target.closest('a[data-nav]');
    if (!link) return;
    if (event.defaultPrevented || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
    const href = link.getAttribute('href');
    if (href == null) return;
    event.preventDefault();
    navigate(href);
  });

  themeBtn.addEventListener('click', () => {
    const next = document.documentElement.dataset.theme === 'dark' ? 'light' : 'dark';
    setTheme(next);
  });

  const sourceBadge = $('#teslaBadge');
  if (sourceBadge) {
    let flashTimer = 0;
    const showSource = () => {
      if (sourceBadge.hidden || !currentVideo) return;
      const defaultText = sourceBadge.dataset.defaultText || 'InMotion';
      if (flashTimer) clearTimeout(flashTimer);
      sourceBadge.textContent = streamSourceLabel(currentVideo);
      sourceBadge.classList.add('source-flash');
      flashTimer = setTimeout(() => {
        sourceBadge.textContent = sourceBadge.dataset.defaultText || defaultText;
        sourceBadge.classList.remove('source-flash');
        flashTimer = 0;
      }, 3000);
    };
    sourceBadge.setAttribute('role', 'button');
    sourceBadge.tabIndex = 0;
    sourceBadge.addEventListener('click', showSource);
    sourceBadge.addEventListener('keydown', (event) => {
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        showSource();
      }
    });
  }

  window.addEventListener('popstate', route);
  document.addEventListener('visibilitychange', () => {
    if (document.hidden || !currentEngine || !currentEngine.live) return;
    const live = currentEngine.live;
    const player = currentEnginePlayer;
    const isVod = !!live.vod;
    const target = (isVod && player) ? player.currentTime : currentEngine.state().currentTime;
    if (isVod && player) currentEngine.syncTo(target);
    currentEngine.catchUp(target);
    currentEngine.setVideoPaused(player ? player.paused : false);
  });
  window.addEventListener('pageshow', (event) => {
    if (event.persisted) route();
  });

  try {
    if (localStorage.getItem('dltube-guide') === 'closed') {
      document.body.classList.add('guide-closed');
    }
  } catch (e) {}

  setTheme(document.documentElement.dataset.theme === 'dark' ? 'dark' : 'light');
  route();
})();
