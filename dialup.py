#!/usr/bin/env python3
"""
NOTE: THIS PROGRAM HAS BEEN MADE WITH THE ASSISTANCE OF MULTIPLE AIs.
THIS PROGRAM WAS TESTED MULTIPLE TIMES DURING DEVELOPMENT.

Dial-up modem simulator (single file) - local two-sided V.90 / ISDN simulation.

This program is intended to run on Linux only.  It uses the terminal
curses API and spawns ALSA 'aplay' via subprocess for real-time PCM;
paths and utilities are not abstracted for Windows or macOS.  Making it
cross-platform would require a different audio sink (native APIs or a
portable library), TUI adjustments, and validation on those OSes.

Requirements
------------
- Python 3.6 or newer.
- Standard library only (no pip packages).
- Recommended: alsa-utils package with 'aplay' on PATH for audible handshake
  and carrier output.  If aplay is missing, the emulator still runs with
  timing and logs in sync, but the audio is silent.

Run:  python3 dialup.py

What it does
------------
- Split view: customer modem log plus waveform vs ISP server log plus waveform.
- A phone-line strip: phase bar, signal/RX/TX/SNR meters, negotiated rate and
  byte counts, optional MLPPP link status tiles, fake HTTP lines, and optional
  page-load progress.
- Analog V.90-style audio: dial tone -> DTMF -> ringback -> CED (2100 Hz plus
  phase reversals) -> ANSam (15 Hz AM) -> optional USR bong -> V.21 FSK ->
  profile-specific V.34/V.90 negotiation (multi-tone bursts and sweeps) ->
  steady carrier while online.
- ISDN TA paths (BRI 64k, BRI 128k with MLPPP, PRI): shorter digital-style
  phases (Q.931 / LAPD / PPP flavour), quieter than analog.
- Modem profiles with distinct timbre and timing: USRobotics Sportster 56K,
  Hayes Optima 56K, Zoom 56K (budget), Motorola ModemSURFR 56K.
- Failure injection on analog attempts (random training scenarios and redial)
  with configurable max attempts and optional per-scenario weights.
- Sound schemes (noisy line, clean DSP, retro 28.8k, silent, etc.) scale
  synthesis noise and jitter from the startup menu.
- MLPPP (1-20 links): simultaneous vs serial bonding; each extra link dials and
  trains with per-link tone detuning; a synthetic multilink LCP / IPCP burst
  after all links are up; aggregate bps tracked for simulation and UI.

Startup menu
------------
Pick modem, failure rate, ISP listing, retry budget, optional advanced failure
weights, sound scheme, and MLPPP count / bonding mode.

Keys: arrows, Tab / Shift-Tab, Space toggles accordions, Enter confirms and
connects, + / - or ] / [ volume, D debug, Q / Esc exit.

Main session (connected and dialling UI)
----------------------------------------
Q              Quit / end session
+ / -  ] / [   Playback volume (global PCM scaler)
D              Toggle debug strip on the phone line panel
W              Fake HTTP page load over PPP (only when ONLINE; otherwise a
               modal message; Enter dismisses)
C / I          Customer or ISP control overlay (toggle)
PgUp / PgDn    Scroll customer log
Mouse wheel    Scroll the log under the pointer (left = customer, right = ISP)

In overlays: Up/Down move, Enter runs the selected action, Esc / X closes.
Speaker, noise, shaping, caps, latency, call-waiting, and similar actions
apply during dialling where meaningful.  Forced hang-up / ATZ / NAS-style
actions raise DialAbort while not yet ONLINE.  Actions that need a finished
link (e.g. +MS retrain) open an error modal.

Customer actions include: line noise toggle, speaker mute (relay click),
ATH / ATZ (abort dial or drop when up), call-waiting beep, line retrain when
connected.

ISP actions include: force client disconnect, NAS port reset, line degrade
(noise plus jitter), upstream noise toggle, 28.8k rate cap, clear cap,
additive shaper latency.

Implementation notes
--------------------
- A sequencer thread drives the call (dial, negotiate, MLPPP, online loop,
  hang-up); the curses UI runs on the main thread.
- Audio is mono S16LE at 8 kHz, written to aplay if available.  pack() applies
  volume, optional scheme silence, speaker path mute, and line-quality mixes
  so operator toggles affect all queued audio, including mid-dial DTMF and
  ringing.
"""

import curses, dataclasses, math, queue, random, struct
import subprocess, threading, time
from typing import List, Tuple, Optional


class DialAbort(Exception):
    """Raised when the user aborts dialling from the control overlay (ATH / ATZ / ISP drop)."""


def _profile_speed_bps(profile: "ModemProfile") -> int:
    """Numeric line rate from profile.max_speed string."""
    return int("".join(c for c in str(profile.max_speed) if c.isdigit()) or "0")


# ─────────────────────────────────────────────────────────────────────────────
# AUDIO ENGINE
# ─────────────────────────────────────────────────────────────────────────────
SR  = 8000          # sample rate Hz
AMP = 26000         # peak amplitude

# global volume multiplier (0.0 – 2.0), modified by +/- keys
_vol     = 1.0
_vol_min = 0.0
_vol_max = 2.0
_vol_step = 0.1

# ── Sound scheme globals (set from startup menu) ──────────────────────────
# (label, noise_mult, jitter_mult, force_silent)
_SOUND_SCHEMES = [
    ("V.90 Standard",  1.0,  1.0, False),
    ("Noisy Line",     2.5,  2.0, False),
    ("Clean DSP",      0.3,  0.2, False),
    ("Retro 28.8K",    1.8,  3.0, False),
    ("Silent",         1.0,  1.0, True ),
]
_scheme_idx          = 0
_scheme_noise_mult   = 1.0   # multiplied into profile.noise_floor
_scheme_jitter_mult  = 1.0   # multiplied into carrier_jitter
_scheme_force_silent = False  # if True, pack() returns raw silence

def _s(freq: float, n: int, amp: int = AMP, ph: float = 0.0) -> List[int]:
    return [int(amp * math.sin(2*math.pi*freq*i/SR + ph)) for i in range(n)]

def _noise(n: int, amp: int) -> List[int]:
    return [random.randint(-amp, amp) for _ in range(n)]

def _hpf(buf: List[int], fc: float) -> List[int]:
    """Single-pole high-pass IIR."""
    a = math.exp(-2*math.pi*fc/SR)
    y, prev = 0.0, 0.0
    out = []
    for x in buf:
        y = a*(y + x - prev); prev = x; out.append(int(y))
    return out

def _lpf(buf: List[int], fc: float) -> List[int]:
    """Single-pole low-pass IIR."""
    a = 1.0 - math.exp(-2*math.pi*fc/SR)
    y = 0.0; out = []
    for x in buf:
        y += a*(x - y); out.append(int(y))
    return out

def _bandpass(n: int, amp: int, lo: float = 300.0, hi: float = 3400.0) -> List[int]:
    return _lpf(_hpf(_noise(n, amp), lo), hi)

def _narrowband(n: int, amp: int, center: float, bw: float = 200.0) -> List[int]:
    """Narrow bandpass noise around a center frequency."""
    lo = max(100.0, center - bw/2)
    hi = min(4000.0, center + bw/2)
    return _lpf(_hpf(_noise(n, amp), lo), hi)

def _mix(layers: List[List[int]]) -> List[int]:
    if not layers: return []
    L = max(len(b) for b in layers)
    d = max(1, len(layers))
    out = [max(-32767, min(32767,
               sum(b[i] if i < len(b) else 0 for b in layers) // d))
           for i in range(L)]
    return out

def _env(buf: List[int], att: float = 0.008, rel: float = 0.015) -> List[int]:
    n, a, r = len(buf), max(1,int(SR*att)), max(1,int(SR*rel))
    out = list(buf)
    for i in range(min(a,n)):  out[i]     = int(out[i]*i/a)
    for i in range(min(r,n)):  out[n-1-i] = int(out[n-1-i]*i/r)
    return out

def _soft_clip(buf: List[int], threshold: int = 28000) -> List[int]:
    """Soft saturation clipping -- prevents harsh digital clipping."""
    out = []
    for x in buf:
        if abs(x) <= threshold:
            out.append(x)
        else:
            sign = 1 if x > 0 else -1
            excess = abs(x) - threshold
            soft   = threshold + excess // 3
            out.append(sign * min(32767, soft))
    return out

def _vol_scale(buf: List[int]) -> List[int]:
    v = _vol
    if v == 1.0: return buf
    raw = [int(x*v) for x in buf]
    return _soft_clip(raw)

def silence(s: float) -> List[int]:
    return [0]*int(SR*s)

def _apply_playback_fx(samples: List[int]) -> List[int]:
    """
    Per-buffer effects for queued PCM: speaker mute, line-noise injections.
    Used for every sound including dial-up so controls work during dialling.
    """
    if not samples:
        return samples
    try:
        st = _state
    except NameError:
        return samples
    if not getattr(st, "speaker_enabled", True):
        return [0] * len(samples)
    layers = [samples]
    if getattr(st, "inject_noise", False):
        layers.append(_bandpass(len(samples), int(AMP * 0.055)))
    if getattr(st, "isp_upstream_noise", False):
        layers.append(_narrowband(len(samples), int(AMP * 0.04), 2650.0, bw=280.0))
    if len(layers) > 1:
        samples = _mix(layers)
    return samples


def pack(s: List[int]) -> bytes:
    if _scheme_force_silent:
        return bytes(len(s) * 2)   # silence without skipping timing
    s = _apply_playback_fx(s)
    return struct.pack(f'<{len(s)}h', *_vol_scale(s))

# ── Modem-sound primitives ────────────────────────────────────────────────────

def dial_tone(s: float = 0.35) -> List[int]:
    """350 + 440 Hz US PSTN dial."""
    n = int(SR*s)
    return _env(_mix([_s(350,n,int(AMP*0.55)), _s(440,n,int(AMP*0.55))]), 0.02, 0.04)

def call_waiting_tone() -> List[int]:
    """US-style call-waiting alert  --  ~440 Hz beep doublet on the line."""
    n = int(SR * 0.1)
    gap = silence(0.08)
    beep = _env(_s(440, n, int(AMP * 0.35)), 0.004, 0.012)
    return beep + gap + beep + silence(0.05)


def busy_tone(cycles: int = 3) -> List[int]:
    """480 + 620 Hz US busy signal -- 0.5 s on / 0.5 s off."""
    n = int(SR*0.5)
    one = _env(_mix([_s(480,n,int(AMP*0.5)), _s(620,n,int(AMP*0.5))]), 0.01, 0.01)
    return (one + silence(0.5)) * cycles

def reorder_tone(cycles: int = 2) -> List[int]:
    """480 + 620 Hz fast busy -- 0.25 s on / 0.25 s off (reorder / path congested)."""
    n = int(SR*0.25)
    one = _env(_mix([_s(480,n,int(AMP*0.45)), _s(620,n,int(AMP*0.45))]), 0.005, 0.005)
    return (one + silence(0.25)) * cycles

def dtmf(digit: str, on: float = 0.10, off: float = 0.055) -> List[int]:
    T = {'1':(697,1209),'2':(697,1336),'3':(697,1477),
         '4':(770,1209),'5':(770,1336),'6':(770,1477),
         '7':(852,1209),'8':(852,1336),'9':(852,1477),
         '0':(941,1336),'*':(941,1209),'#':(941,1477)}
    if digit not in T: return silence(on+off)
    r,c = T[digit]; n = int(SR*on)
    # Add a tiny bit of telephone line character noise under the DTMF tones
    noise_layer = _bandpass(n, int(AMP*0.03))
    tone = _env(_mix([_s(r,n,int(AMP*0.48)), _s(c,n,int(AMP*0.48)), noise_layer]), 0.004, 0.008)
    return tone + silence(off)

def ringback(cycles: int = 1) -> List[int]:
    """440+480 Hz  --  2 s on / 4 s off (US PSTN standard ringback cadence)."""
    n = int(SR*2.0)
    ring = _env(_mix([_s(440,n,int(AMP*0.5)), _s(480,n,int(AMP*0.5))]), 0.02, 0.04)
    # slight line noise between rings for realism
    gap = silence(3.5) + _bandpass(int(SR*0.5), int(AMP*0.02))
    return (ring + gap) * cycles

def ced_tone(duration: float = 3.3) -> List[int]:
    """
    CED: 2100 Hz with 180-degree phase reversal every 450 ms.
    The phase flip is what gives the characteristic 'pulsed beep' quality.
    Spec: ITU-T V.25 -- answering tone disables echo suppressors.
    """
    n, seg = int(SR*duration), int(SR*0.45)
    amp = int(AMP*0.72); ph = 0.0; out = []
    for i in range(n):
        if i > 0 and i % seg == 0:
            ph = math.pi - ph          # 180° phase reversal
        out.append(int(amp * math.sin(2*math.pi*2100*i/SR + ph)))
    # Add soft telephone line noise under CED
    noise = _bandpass(n, int(AMP*0.04))
    mixed = _mix([out, noise])
    return _env(mixed, 0.02, 0.02)

def ansam(duration: float = 0.80) -> List[int]:
    """
    ANSam: 2100 Hz carrier amplitude-modulated at 15 Hz.
    V.8-capable modems send this instead of plain CED to signal V.8 support.
    The 15 Hz AM sideband is the fingerprint that V.8 is being offered.
    """
    n   = int(SR*duration); amp = int(AMP*0.68)
    out = [int(amp * (1.0 + 0.15*math.sin(2*math.pi*15*i/SR))
                   * math.sin(2*math.pi*2100*i/SR))
           for i in range(n)]
    noise = _bandpass(n, int(AMP*0.03))
    return _env(_mix([out, noise]), 0.01, 0.02)

def v21_fsk(channel: int, duration: float, noise_floor: float = 0.06) -> List[int]:
    """
    V.21 FSK flag sequence.
    Ch1 (originate): mark=1080 Hz / space=980 Hz  @ 300 baud
    Ch2 (answer):    mark=1650 Hz / space=1750 Hz @ 300 baud
    Each channel uses continuous-phase FSK (CPFSK).
    """
    mark, space = (1080, 980) if channel == 1 else (1650, 1750)
    baud   = 300
    bit_n  = SR // baud
    n      = int(SR*duration)
    bits   = [0,1,1,1,1,1,1,0] * (n//(8*bit_n)+2)   # HDLC 0x7E flags
    ph     = 0.0; out = []
    for i in range(n):
        f   = mark if bits[(i//bit_n) % len(bits)] else space
        ph += 2*math.pi*f/SR
        out.append(int(AMP*0.50 * math.sin(ph)))
    noise = _bandpass(n, int(AMP*noise_floor))
    return _env(_mix([out, noise]), 0.005, 0.008)

def handshake_burst(freqs:  List[float],
                    dur:    float,
                    fm:     float = 0.025,
                    nmix:   float = 0.15,
                    nfloor: float = 0.08,
                    harmonics: bool = False,
                    amp_scale: float = 1.0) -> List[int]:
    """
    Multi-tone burst with FM jitter + band-limited noise.
    freqs     : fundamental frequencies (Hz)
    fm        : FM depth (0 = clean sines)
    nmix      : noise fraction of total amplitude
    nfloor    : modem's noise-floor level multiplier
    harmonics : add 2nd harmonic distortion (makes cheap modems sound nastier)
    amp_scale : master amplitude scaler (differentiates modem volume characters)
    """
    n       = int(SR*dur)
    amp_per = int(AMP * amp_scale * (1.0-nmix) / max(1,len(freqs)))
    layers  = []
    for f in freqs:
        ph = 0.0; buf = []
        for i in range(n):
            jitter = 1.0 + fm*math.sin(2*math.pi*6.3*i/SR + random.uniform(0,.05))
            ph    += 2*math.pi*f*jitter/SR
            sample = amp_per*math.sin(ph)
            if harmonics:
                # 2nd harmonic at -12 dB adds analogue distortion character
                sample += (amp_per*0.25)*math.sin(2*ph)
            buf.append(int(sample))
        layers.append(buf)
    noise_amp = int(AMP*nmix*max(0.5, nfloor*8))
    layers.append(_bandpass(n, noise_amp))
    return _env(_mix(layers), 0.012, 0.018)

def freq_sweep(f0: float, f1: float, dur: float,
               amp_frac: float = 0.58, noise_mix: float = 0.05) -> List[int]:
    """Linear frequency sweep -- line probing / pilot tones."""
    n  = int(SR*dur); ph = 0.0; out = []
    for i in range(n):
        f   = f0 + (f1-f0)*i/n
        ph += 2*math.pi*f/SR
        out.append(int(AMP*amp_frac*math.sin(ph)))
    noise = _bandpass(n, int(AMP*noise_mix))
    return _env(_mix([out, noise]), 0.008, 0.012)

def carrier_hum(freq: float = 1800.0, dur: float = 0.5,
                amp_frac: float = 0.20, jitter: float = 0.0) -> List[int]:
    """
    Steady carrier tone -- heard continuously while connected.
    jitter > 0 adds slight frequency wobble (budget modem characteristic).
    """
    n = int(SR*dur)
    if jitter == 0.0:
        buf = _s(freq, n, int(AMP*amp_frac))
    else:
        ph = 0.0; buf = []
        for i in range(n):
            f   = freq + jitter * math.sin(2*math.pi*1.7*i/SR)
            ph += 2*math.pi*f/SR
            buf.append(int(AMP*amp_frac*math.sin(ph)))
    return _env(buf, 0.05, 0.05)

def floppy_disk_eject_sound() -> List[int]:
    """Spin-down + thunk — swap disk / drive door during PPP."""
    n = int(SR * 0.38)
    out: List[int] = []
    for i in range(n):
        t = i / SR
        f = 720.0 * (1.0 - i / n) + 45.0
        amp = int(AMP * 0.11 * math.exp(-2.2 * t))
        out.append(int(amp * math.sin(2 * math.pi * f * t + 0.02 * math.sin(80 * t))))
    return _env(out + speaker_click(0.24) + line_noise_burst(0.06, 0.16), 0.01, 0.02)


def floppy_disk_insert_sound() -> List[int]:
    """Chunk + motor spin-up after inserting a new demo disk."""
    chunk = speaker_click(0.32) + line_noise_burst(0.045, 0.22)
    n = int(SR * 0.42)
    ph = 0.0
    up: List[int] = []
    for i in range(n):
        f = 180.0 + 780.0 * (i / n) ** 0.85
        ph += 2 * math.pi * f / SR
        mul = (i / n) ** 1.2
        up.append(int(AMP * 0.095 * mul * math.sin(ph)))
    return _env(chunk + up, 0.008, 0.018)


def speaker_click(amp_frac: float = 0.30) -> List[int]:
    """
    Modem speaker relay click -- heard when AT command enables speaker.
    A short mechanical transient, very brief.
    """
    n = int(SR*0.012)
    # Decaying impulse response mimicking a relay click
    out = []
    for i in range(n):
        decay = math.exp(-i / (SR*0.004))
        out.append(int(AMP*amp_frac * decay * (1 if i%2==0 else -1)))
    return _env(out, 0.0005, 0.003)

def disconnect_crackle() -> List[int]:
    """Line disconnect -- broadband burst then silence."""
    n1 = int(SR*0.08)
    n2 = int(SR*0.04)
    burst  = _env(_bandpass(n1, int(AMP*0.55)), 0.001, 0.020)
    burst2 = _env(_bandpass(n2, int(AMP*0.30)), 0.001, 0.015)
    return burst + silence(0.05) + burst2

def line_noise_burst(dur: float = 0.12, amp_frac: float = 0.18) -> List[int]:
    """Random line noise burst -- adds realism to idle/ringing periods."""
    return _env(_bandpass(int(SR*dur), int(AMP*amp_frac)), 0.003, 0.010)

# ── USRobotics-specific sounds ────────────────────────────────────────────────

def usr_bong() -> List[int]:
    """
    USRobotics Sportster characteristic startup arpeggio.
    Three-note ascending chord sequence heard immediately after carrier detect.
    The chord intervals (880/1320, 1100/1650, 1320/2200) are USR's acoustic
    signature -- instantly recognisable to anyone who used the internet in the 90s.
    """
    n1, n2, n3 = int(SR*0.14), int(SR*0.16), int(SR*0.18)
    c1 = _env(_mix([_s(880, n1,AMP//2), _s(1320,n1,AMP//2)]), 0.006, 0.030)
    c2 = _env(_mix([_s(1100,n2,AMP//2), _s(1650,n2,AMP//2)]), 0.006, 0.030)
    c3 = _env(_mix([_s(1320,n3,AMP//2), _s(2200,n3,AMP//2)]), 0.006, 0.040)
    return c1 + silence(0.032) + c2 + silence(0.032) + c3

def usr_probe_sweep() -> List[int]:
    """USR's characteristic bidirectional probe sweep during negotiation."""
    s1 = freq_sweep(300,  3400, 0.22, amp_frac=0.62, noise_mix=0.04)
    s2 = freq_sweep(3400, 1800, 0.18, amp_frac=0.54, noise_mix=0.04)
    return s1 + silence(0.02) + s2

# ── Hayes-specific sounds ─────────────────────────────────────────────────────

def hayes_init_tone() -> List[int]:
    """
    Hayes Optima clean single-frequency probe -- textbook V.34 quality.
    A brief 1800 Hz pilot before the main negotiation, precise and uncoloured.
    """
    n = int(SR*0.18)
    return _env(_s(1800, n, int(AMP*0.55)), 0.008, 0.012)

def hayes_probe_sweep() -> List[int]:
    """Hayes V.34 line probe -- single direction, clinical precision."""
    return freq_sweep(600, 3200, 0.28, amp_frac=0.60, noise_mix=0.025)

# ── Zoom-specific sounds ──────────────────────────────────────────────────────

def pop_static(amp_frac: float = 0.45) -> List[int]:
    """Random static crackle -- budget Zoom hardware character."""
    dur = random.uniform(0.025, 0.055)
    return _env(_bandpass(int(SR*dur), int(AMP*amp_frac)), 0.001, 0.004)

def zoom_grind() -> List[int]:
    """
    Zoom's distinctive 'grinding' mid-negotiation noise.
    Rapid FM-heavy tones with heavy noise -- the Zoom budget hardware signature.
    """
    n = int(SR*0.32)
    ph = 0.0; buf = []
    for i in range(n):
        # Fast FM sweep between 800-2400 Hz
        f   = 1600 + 800*math.sin(2*math.pi*4.5*i/SR)
        ph += 2*math.pi*f/SR
        buf.append(int(AMP*0.40*math.sin(ph)))
    noise = _bandpass(n, int(AMP*0.28))
    return _env(_mix([buf, noise]), 0.005, 0.015)

def zoom_static_burst() -> List[int]:
    """Zoom line static -- heavy broadband noise that interrupts negotiation."""
    n = int(SR*0.06)
    return _env(_bandpass(n, int(AMP*0.50)), 0.001, 0.010)

# ── Motorola-specific sounds ──────────────────────────────────────────────────

def moto_highfreq_burst(freqs: List[float], dur: float) -> List[int]:
    """
    Motorola SURFR high-frequency emphasis burst.
    Uses frequencies > 2000 Hz aggressively -- brighter, sharper sound than USR/Hayes.
    Very low noise floor -- Motorola was known for clean DSP.
    """
    n = int(SR*dur)
    amp_per = int(AMP*0.62 / max(1,len(freqs)))
    layers  = []
    for f in freqs:
        ph = 0.0; buf = []
        for i in range(n):
            # Very tight FM (Motorola's clean DSP)
            jitter = 1.0 + 0.004*math.sin(2*math.pi*8.1*i/SR)
            ph    += 2*math.pi*f*jitter/SR
            buf.append(int(amp_per*math.sin(ph)))
        layers.append(buf)
    # Motorola has minimal noise -- very clean hardware
    layers.append(_bandpass(n, int(AMP*0.04)))
    return _env(_mix(layers), 0.008, 0.012)

def moto_probe_sweep() -> List[int]:
    """Motorola SURFR rapid high-frequency probe sweep."""
    # Much faster than USR/Hayes, starts high
    s1 = freq_sweep(2200, 3400, 0.14, amp_frac=0.65, noise_mix=0.02)
    s2 = freq_sweep(3400,  800, 0.12, amp_frac=0.60, noise_mix=0.02)
    return s1 + s2

def moto_connect_chirp() -> List[int]:
    """Motorola's brief high chirp just before CONNECT -- their audio signature."""
    n = int(SR*0.08)
    ph = 0.0; buf = []
    for i in range(n):
        f   = 2800 + 600*(i/n)
        ph += 2*math.pi*f/SR
        buf.append(int(AMP*0.35*math.sin(ph)))
    return _env(buf, 0.004, 0.008)


# ─────────────────────────────────────────────────────────────────────────────
# ISDN AUDIO PRIMITIVES
# ─────────────────────────────────────────────────────────────────────────────

def isdn_dial_tone(s: float = 0.25) -> List[int]:
    """425 Hz dial tone (ITU-T/European ISDN standard, clean digital)."""
    n = int(SR * s)
    return _env(_s(425, n, int(AMP * 0.60)), 0.01, 0.02)

def isdn_setup_beep() -> List[int]:
    """D-channel SETUP indication -- brief clean 800 Hz pulse."""
    n = int(SR * 0.06)
    return _env(_s(800, n, int(AMP * 0.50)), 0.003, 0.008)

def isdn_progress_tone(cycles: int = 1) -> List[int]:
    """Ringback on ISDN line: cleaner 425 Hz on/off cadence."""
    on_n  = int(SR * 1.0)
    off_n = int(SR * 3.0)
    tone  = _env(_s(425, on_n, int(AMP * 0.55)), 0.01, 0.02)
    return (tone + silence(3.0)) * cycles

def isdn_bchan_activate() -> List[int]:
    """
    B-channel activation burst: rapid 8 kHz digital sync,
    sounds like a short precise digital chirp -- no analog hiss.
    """
    n  = int(SR * 0.08)
    ph = 0.0; buf = []
    for i in range(n):
        f   = 4000 + 3000 * (i / n)   # fast rising sweep, very clean
        ph += 2 * math.pi * f / SR
        buf.append(int(AMP * 0.45 * math.sin(ph)))
    noise = _bandpass(n, int(AMP * 0.015))  # nearly noiseless
    return _env(_mix([buf, noise]), 0.002, 0.006)

def isdn_connect_confirm() -> List[int]:
    """Clean two-tone CONNECT confirmation -- ISDN terminal adaptor style."""
    n1 = int(SR * 0.07)
    n2 = int(SR * 0.09)
    t1 = _env(_s(2048, n1, int(AMP * 0.40)), 0.003, 0.008)
    t2 = _env(_s(4096, n2, int(AMP * 0.35)), 0.003, 0.008)
    return t1 + silence(0.015) + t2

def isdn_hangup_beep() -> List[int]:
    """ISDN release: short descending two-beep sequence."""
    n1 = int(SR * 0.07)
    n2 = int(SR * 0.07)
    b1 = _env(_s(1000, n1, int(AMP * 0.40)), 0.003, 0.010)
    b2 = _env(_s(500,  n2, int(AMP * 0.35)), 0.003, 0.012)
    return b1 + silence(0.04) + b2 + silence(0.05)

def isdn_dummy_sweep() -> List[int]:
    """Placeholder sweep for ISDN profiles (no analog sweep needed)."""
    return isdn_bchan_activate()

# ─────────────────────────────────────────────────────────────────────────────
# MODEM PROFILES
# Each phase entry: (label, [freqs Hz], fm_depth, noise_mix, base_dur_s)
# ─────────────────────────────────────────────────────────────────────────────

_USR = (
    ("V.21 Ch1  --  calling modem flags",   [1080],                     0.010, 0.07, 0.55),
    ("V.8 CM  --  capability offer",        [1050, 2100],               0.018, 0.09, 0.45),
    ("V.8 JM  --  modulation agreed V.90",  [2100, 2400],               0.016, 0.10, 0.45),
    ("V.90 phase A  --  HI pilot tones",    [2400, 2800, 3200],         0.028, 0.13, 0.42),
    ("V.90 phase A  --  LO pilot tones",    [600,  1200, 1800],         0.026, 0.12, 0.42),
    ("V.90 phase B  --  equaliser train",   [900, 1600, 2400, 3100],    0.032, 0.16, 0.48),
    ("V.90 phase C  --  trellis sync",      [1200, 2400, 3200],         0.022, 0.11, 0.42),
    ("V.90 phase D  --  rate renegotiation",[1800, 2600],               0.014, 0.09, 0.38),
    ("V.42 LAPM  --  frame exchange",       [1800, 2800],               0.009, 0.07, 0.35),
    ("V.42bis  --  dictionary init",        [1800],                     0.006, 0.05, 0.30),
    ("PPP LCP  --  link negotiation",       [1800, 2100],               0.004, 0.03, 0.28),
    ("PPP IPCP  --  address assignment",    [1800],                     0.002, 0.02, 0.22),
)

_HAYES = (
    ("V.21 flags  --  clean originate",     [1080],                     0.006, 0.04, 0.50),
    ("V.8 CM  --  precise capability offer",[1050, 2100],               0.010, 0.05, 0.42),
    ("V.8 JM  --  V.34 agreed",             [2100],                     0.009, 0.06, 0.40),
    ("V.34 probing HI  --  line analysis",  [2600, 3000, 3200],         0.016, 0.08, 0.42),
    ("V.34 probing LO  --  echo measure",   [700,  1400, 2100],         0.014, 0.07, 0.42),
    ("V.34 equaliser train  --  precision", [900, 1800, 2700, 3100],    0.020, 0.10, 0.46),
    ("V.34 precoding + trellis coding",     [1400, 2400, 3000],         0.013, 0.07, 0.42),
    ("V.34 rate selection",                 [1800, 2600],               0.009, 0.06, 0.38),
    ("V.42 LAPM  --  frame handshake",      [2000, 2800],               0.007, 0.04, 0.32),
    ("V.42bis dictionary init",             [1800],                     0.004, 0.03, 0.28),
    ("PPP LCP  --  link negotiation",       [1800, 2100],               0.002, 0.02, 0.26),
    ("PPP IPCP  --  address assignment",    [1800],                     0.001, 0.01, 0.22),
)

_ZOOM = (
    ("V.21 flags  --  noisy line",          [1080],                     0.016, 0.18, 0.58),
    ("V.8 CM  --  interference",            [1050, 2100],               0.030, 0.22, 0.50),
    ("V.8 JM  --  barely agreed",           [2100, 2200],               0.026, 0.24, 0.48),
    ("V.34 HI  --  high noise floor",       [2200, 2700, 3100],         0.044, 0.28, 0.52),
    ("V.34 LO  --  heavy static pops",      [500,  1100, 1800],         0.042, 0.26, 0.54),
    ("Equaliser  --  hostile environment",  [800, 1500, 2200, 3000],    0.050, 0.32, 0.60),
    ("Trellis coding  --  degraded",        [1100, 2200, 3000],         0.034, 0.24, 0.50),
    ("Rate renegotiation  --  downgrade",   [1800, 2600],               0.020, 0.20, 0.46),
    ("V.42 LAPM  --  retransmit",           [1800, 2800],               0.020, 0.16, 0.42),
    ("V.42bis  --  partial dict",           [1800],                     0.012, 0.12, 0.35),
    ("PPP LCP  --  negotiating",            [1800, 2000],               0.008, 0.08, 0.32),
    ("PPP IPCP  --  finalising",            [1800],                     0.005, 0.06, 0.28),
)

_MOTO = (
    ("V.21 flags  --  fast originate",      [1080],                     0.005, 0.03, 0.30),
    ("V.8 CM  --  rapid capability offer",  [1050, 2100],               0.009, 0.04, 0.25),
    ("V.8 JM  --  V.90 fast lock",          [2100],                     0.007, 0.05, 0.22),
    ("V.90 HI  --  rapid HF probe",         [2800, 3100, 3400],         0.018, 0.06, 0.24),
    ("V.90 LO  --  rapid LF probe",         [600,  1400, 2200],         0.016, 0.06, 0.24),
    ("Equaliser  --  DSP precision",        [1000, 2000, 3000, 3400],   0.020, 0.07, 0.28),
    ("Trellis sync  --  fast lock",         [1600, 2800, 3200],         0.014, 0.06, 0.22),
    ("Rate  --  rapid renegotiation",       [2000, 3000, 3400],         0.007, 0.04, 0.20),
    ("V.42 LAPM  --  high efficiency",      [2000, 3000],               0.005, 0.03, 0.18),
    ("V.42bis  --  fast dict build",        [1800],                     0.003, 0.02, 0.16),
    ("PPP LCP  --  fast path",              [1800, 2100],               0.002, 0.01, 0.15),
    ("PPP IPCP  --  rapid address assign",  [1800],                     0.001, 0.01, 0.13),
)


# ISDN phase tables
_ISDN_BRI_64 = (
    ("Q.931 SETUP  --  D-channel ISDN signal",    [425],            0.001, 0.003, 0.10),
    ("Q.931 CALL PROCEEDING",                     [425, 800],       0.001, 0.003, 0.08),
    ("Q.931 ALERTING  --  remote ringing",        [425],            0.001, 0.002, 0.18),
    ("Q.931 CONNECT  --  call accepted",          [2048],           0.001, 0.002, 0.07),
    ("LAPD SABME  --  layer-2 link setup",        [2048, 4096],     0.001, 0.002, 0.10),
    ("LAPD UA  --  link established",             [4096],           0.001, 0.001, 0.07),
    ("PPP LCP  --  negotiate link params",        [2048, 4096],     0.001, 0.002, 0.12),
    ("PPP IPCP  --  IP address negotiation",      [2048],           0.001, 0.001, 0.10),
)

_ISDN_BRI_128 = (
    ("Q.931 SETUP  --  D-channel signal (2 B)",   [425],            0.001, 0.003, 0.10),
    ("Q.931 CALL PROCEEDING  --  both B-ch",      [425, 800],       0.001, 0.003, 0.08),
    ("Q.931 ALERTING",                            [425],            0.001, 0.002, 0.15),
    ("Q.931 CONNECT  --  B1 channel up",          [2048],           0.001, 0.002, 0.07),
    ("Q.931 CONNECT  --  B2 channel up",          [4096],           0.001, 0.002, 0.07),
    ("LAPD  --  layer-2 on both B-channels",      [2048, 4096],     0.001, 0.002, 0.10),
    ("MLPPP LCP  --  bundle negotiation",         [2048, 4096],     0.001, 0.002, 0.12),
    ("MLPPP IPCP  --  IP over bonded channels",   [2048],           0.001, 0.001, 0.10),
)

_ISDN_PRI = (
    ("PRI D-channel  --  Q.931 SETUP",            [425],            0.001, 0.001, 0.08),
    ("PRI CALL PROCEEDING",                       [425, 800],       0.001, 0.001, 0.06),
    ("PRI ALERTING",                              [425],            0.001, 0.001, 0.10),
    ("PRI CONNECT  --  30 B-channels up",         [2048],           0.001, 0.001, 0.06),
    ("LAPD  --  E1/T1 framing sync",              [2048, 4096],     0.001, 0.001, 0.08),
    ("MLPPP  --  30-channel bundle",              [4096],           0.001, 0.001, 0.08),
    ("PPP LCP  --  negotiate PRI params",         [2048, 4096],     0.001, 0.001, 0.10),
    ("PPP IPCP  --  PRI address assign",          [2048],           0.001, 0.001, 0.08),
)

@dataclasses.dataclass
class ModemProfile:
    name:         str
    short:        str
    max_speed:    str
    noise_floor:  float     # 0.0=clean, higher=noisier hardware
    timing_mult:  float     # 1.0=standard; 0.7=fast
    has_bong:     bool      # USR-specific startup chord
    carrier_freq: float     # connected carrier frequency (Hz)
    carrier_jitter: float   # carrier frequency wobble (0=stable)
    carrier_amp:  float     # carrier amplitude fraction
    compression:  str
    description:  str
    phases:       tuple     # phase definitions
    sweep_fn:     object    # function that generates probe sweep audio
    init_fn:      object    # optional function for modem-specific init sound
    harmonics:    bool      # whether to add 2nd harmonic distortion
    is_isdn:      bool = False  # True => skip analog handshake, use ISDN sequence

PROFILES = [
    ModemProfile(
        "USRobotics Sportster 56K V.90", "USR Sportster",
        "56000", 0.08, 1.00, True,
        carrier_freq=1800.0, carrier_jitter=0.0, carrier_amp=0.22,
        compression="V.42bis",
        description="Industry standard.  Famous 3-note bong + deep resonant negotiation.",
        phases=_USR,
        sweep_fn=usr_probe_sweep,
        init_fn=None,
        harmonics=False,
    ),
    ModemProfile(
        "Hayes Optima 56K V.90", "Hayes Optima",
        "53333", 0.04, 1.05, False,
        carrier_freq=1800.0, carrier_jitter=0.0, carrier_amp=0.18,
        compression="V.42bis",
        description="Classic Hayes quality.  Clean precise V.34, quiet steady carrier.",
        phases=_HAYES,
        sweep_fn=hayes_probe_sweep,
        init_fn=hayes_init_tone,
        harmonics=False,
    ),
    ModemProfile(
        "Zoom 56K V.90  (budget)", "Zoom 56K",
        "49333", 0.28, 0.92, False,
        carrier_freq=1820.0, carrier_jitter=8.5, carrier_amp=0.19,
        compression="V.42bis",
        description="Budget hardware.  Heavy static pops, grinding noise, wobbly carrier.",
        phases=_ZOOM,
        sweep_fn=zoom_grind,
        init_fn=None,
        harmonics=True,
    ),
    ModemProfile(
        "Motorola ModemSURFR 56K", "Moto SURFR",
        "52000", 0.04, 0.65, False,
        carrier_freq=1920.0, carrier_jitter=0.0, carrier_amp=0.16,
        compression="V.42bis",
        description="Fastest negotiation.  High-frequency emphasis, bright clean DSP.",
        phases=_MOTO,
        sweep_fn=moto_probe_sweep,
        init_fn=None,
        harmonics=False,
    ),
    # ── ISDN profiles ───────────────────────────────────────────────────
    ModemProfile(
        "ISDN BRI  64K  (single B-channel)", "ISDN BRI64",
        "64000", 0.01, 0.45, False,
        carrier_freq=4096.0, carrier_jitter=0.0, carrier_amp=0.20,
        compression="V.42bis",
        description="ISDN Basic Rate: 1 x 64 Kbps B-channel.  Near-silent, instant setup.",
        phases=_ISDN_BRI_64,
        sweep_fn=isdn_dummy_sweep,
        init_fn=None,
        harmonics=False,
        is_isdn=True,
    ),
    ModemProfile(
        "ISDN BRI 128K  (2xB-channel bond)", "ISDN BRI128",
        "128000", 0.01, 0.40, False,
        carrier_freq=4096.0, carrier_jitter=0.0, carrier_amp=0.20,
        compression="V.42bis",
        description="ISDN BRI: both B-channels bonded via MLPPP  --  128 Kbps.",
        phases=_ISDN_BRI_128,
        sweep_fn=isdn_dummy_sweep,
        init_fn=None,
        harmonics=False,
        is_isdn=True,
    ),
    ModemProfile(
        "ISDN PRI  2048K  (30xB E1)", "ISDN PRI",
        "2048000", 0.01, 0.30, False,
        carrier_freq=4096.0, carrier_jitter=0.0, carrier_amp=0.18,
        compression="V.42bis",
        description="ISDN Primary Rate: 30 x 64 Kbps B-channels (E1).  Enterprise.",
        phases=_ISDN_PRI,
        sweep_fn=isdn_dummy_sweep,
        init_fn=None,
        harmonics=False,
        is_isdn=True,
    ),
]

FAIL_OPTIONS = [
    ("NONE",   0.00),
    ("LOW",    0.18),
    ("MEDIUM", 0.45),
    ("HIGH",   0.82),
    ("ALWAYS", 2.00),   # sentinel > 1.0  means guaranteed fail every attempt
]

# ── Failure-type audio generators ─────────────────────────────────────────────

def _noise_fail_audio() -> List[int]:
    """SNR collapse: rising broadband noise that swamps the carrier."""
    n    = int(SR * 1.2)
    base = _bandpass(n, int(AMP * 0.55))
    # Amplitude ramp-up -- noise overwhelms the signal
    ramp = [int(base[i] * (0.3 + 0.7 * i / n)) for i in range(n)]
    return _env(ramp, 0.005, 0.10) + disconnect_crackle()

def _training_timeout_audio() -> List[int]:
    """Training timeout: negotiation devolves into reorder tone."""
    decay_n = int(SR * 0.6)
    ph = 0.0; buf = []
    for i in range(decay_n):
        f   = 1800 - 800 * (i / decay_n)   # pitch falls as modem gives up
        ph += 2 * math.pi * f / SR
        amp = int(AMP * 0.45 * (1.0 - 0.6 * i / decay_n))
        buf.append(int(amp * math.sin(ph)))
    noise = _bandpass(decay_n, int(AMP * 0.18))
    fade  = _env(_mix([buf, noise]), 0.01, 0.15)
    return fade + reorder_tone(3) + silence(0.15)

def _busy_fail_audio() -> List[int]:
    """ISP NAS port busy: standard busy cadence after a brief crackle."""
    return line_noise_burst(0.08, 0.25) + silence(0.05) + busy_tone(3)

def _equaliser_fail_audio() -> List[int]:
    """Equaliser divergence: the adaptive equalizer cannot converge -- line too
    impaired for V.90.  Rapid burst of chaotic tones as the DSP gives up."""
    n = int(SR * 0.22)
    ph = 0.0; buf = []
    for i in range(n):
        f   = 1200 + 1800 * abs(math.sin(2 * math.pi * 7 * i / n))
        ph += 2 * math.pi * f / SR
        buf.append(int(AMP * 0.42 * math.sin(ph)))
    noise  = _bandpass(n, int(AMP * 0.28))
    glitch = _env(_mix([buf, noise]), 0.002, 0.012)
    return glitch + reorder_tone(2) + silence(0.1) + disconnect_crackle()

def _remote_hangup_audio() -> List[int]:
    """Remote side hung up cleanly: soft click then silence."""
    return speaker_click(0.22) + silence(0.12) + disconnect_crackle()

# (label shown in status, client log msg, isp log msg, audio_fn)
_FAIL_SCENARIOS: List[Tuple] = [
    ("NO CARRIER",
     "NO CARRIER  (abrupt line drop)",
     "Client dropped  --  TX timeout",
     disconnect_crackle),
    ("BUSY",
     "BUSY  (all ISP ports in use  --  try again)",
     "All NAS ports busy  --  dropping call",
     _busy_fail_audio),
    ("TRAINING TIMEOUT",
     "NO CARRIER  (training timeout  --  negotiation > 60 s)",
     "Training timeout  --  client failed to lock",
     _training_timeout_audio),
    ("EXCESSIVE NOISE",
     "NO CARRIER  (SNR too low  --  line noise too high)",
     "SNR failure  --  noise floor exceeded threshold",
     _noise_fail_audio),
    ("REMOTE HANGUP",
     "NO CARRIER  (remote hang-up  --  ISP NAS reset)",
     "Port reset by NAS  --  session aborted",
     _remote_hangup_audio),
    ("EQUALISER DIVERGED",
     "NO CARRIER  (V.90 equaliser diverged  --  line too impaired for V.90)",
     "Equaliser failed to converge  --  line conditions too poor for V.90",
     _equaliser_fail_audio),
]

def _do_failure(phase_idx: int, n_phases: int,
                weights: Optional[List[float]] = None) -> None:
    """Choose a random failure scenario (optionally weighted), play its audio."""
    if weights and any(w > 0 for w in weights):
        population = [s for s, w in zip(_FAIL_SCENARIOS, weights) if w > 0]
        wts        = [w for w in weights if w > 0]
        label, cmsg, imsg, audio_fn = random.choices(population, weights=wts, k=1)[0]
    else:
        label, cmsg, imsg, audio_fn = random.choice(_FAIL_SCENARIOS)
    audio_buf  = audio_fn()
    phase_info = f"phase {phase_idx+1}/{n_phases}"
    _sync(audio_buf,
          f"<-- {cmsg}  ({phase_info})", "FAIL",
          f"{imsg}  ({phase_info})", "FAIL")
    with _state.lock:
        _state.customer.status = label
        _state.isp.status      = "RESET"
        _state.line_state      = "FAILED"
    _wave('C', 'STATIC'); _wave('I', 'STATIC')
    _stats(0, 0, 0, 0)
    _gap(1.8)

# ISP dial-in numbers -- different digit combinations produce different DTMF patterns
ISP_NUMBERS = [
    ("555-0199",    "dialin.local           --  generic local server"),
    ("555-1212",    "EarthLink NAS          --  regional POP"),
    ("1-800-4357",  "AOL 1-800-4357         --  America Online"),
    ("1-888-6328",  "NetZero 1-888-NETZER   --  free ISP"),
    ("555-8472",    "CompuServe             --  CompuServe GmbH"),
    ("1-888-2669",  "Juno Online 1-888-CONN --  free ISP"),
    ("1-800-9284",  "MCI WorldCom           --  backbone POP"),
    ("555-3141",    "dialup.isp.example.net --  custom number"),
]

def phase_audio(profile: ModemProfile, idx: int) -> List[int]:
    """Generate modem-profile-specific audio for one negotiation phase."""
    eff_jitter = profile.carrier_jitter * _scheme_jitter_mult
    if idx >= len(profile.phases):
        return carrier_hum(profile.carrier_freq, 0.28*profile.timing_mult,
                           profile.carrier_amp, eff_jitter)
    lbl, freqs, fm, nm, base_dur = profile.phases[idx]
    dur = base_dur * profile.timing_mult
    eff_nf = profile.noise_floor * _scheme_noise_mult

    # Zoom: special grinding sound for some phases
    if eff_nf > 0.20 and idx in (5, 6):
        buf = zoom_grind()
    elif profile.carrier_freq >= 1900 and profile.carrier_jitter == 0.0:
        # Motorola: use HF-emphasis burst
        buf = moto_highfreq_burst(freqs, dur)
    else:
        buf = handshake_burst(freqs, dur, fm, nm, eff_nf,
                              harmonics=profile.harmonics)

    # Zoom: random static pops during negotiation
    if eff_nf > 0.15 and random.random() < 0.35:
        buf = buf + pop_static(0.45 * eff_nf)

    # Zoom: occasional static bursts mid-phase
    if eff_nf > 0.20 and random.random() < 0.20:
        buf = zoom_static_burst() + buf

    return buf

def sweep_audio(profile: ModemProfile) -> List[int]:
    """Profile-specific sweep probe."""
    return profile.sweep_fn()


# ─────────────────────────────────────────────────────────────────────────────
# AUDIO PLAYER
# ─────────────────────────────────────────────────────────────────────────────

class AudioPlayer:
    def __init__(self):
        self.ok   = self._probe()
        self._q   = queue.Queue(maxsize=24)
        self._th  = threading.Thread(target=self._worker, daemon=True)
        self._proc: Optional[subprocess.Popen] = None  # kept so stop() can kill it

    def _probe(self) -> bool:
        try:
            return subprocess.run(['which','aplay'],
                                  capture_output=True).returncode == 0
        except Exception:
            return False

    def start(self):
        self._th.start()

    # 20 ms of silence -- written whenever the queue is empty so aplay
    # never starves and "underrun!!!" never appears.
    _SILENCE_CHUNK = struct.pack('<{}h'.format(SR // 50), *([0] * (SR // 50)))

    def _worker(self):
        if not self.ok:
            while True:
                try:
                    if self._q.get(timeout=0.5) is None: return
                except queue.Empty:
                    pass
            return
        proc = subprocess.Popen(
            # Small buffer (40 ms) keeps aplay latency near-zero so that
            # audio starts playing within ~40 ms of being queued.
            ['aplay', '-r', str(SR), '-f', 'S16_LE', '-c', '1', '-q',
             '--buffer-time=40000', '-'],
            stdin=subprocess.PIPE)
        self._proc = proc
        while True:
            try:
                item = self._q.get(timeout=0.001)
                if item is None: break
                proc.stdin.write(pack(item))
            except queue.Empty:
                try:
                    proc.stdin.write(self._SILENCE_CHUNK)
                    proc.stdin.flush()
                except (BrokenPipeError, OSError):
                    break
                continue
            except (BrokenPipeError, OSError):
                break
        try: proc.stdin.close()
        except Exception: pass

    def play(self, buf: List[int]):
        try:    self._q.put_nowait(buf)
        except queue.Full: pass

    def play_now(self, buf: List[int]):
        """Clear queue and immediately play -- used for urgent sounds."""
        self.clear()
        self.play(buf)

    def clear(self):
        """Drain the queue (used on hang-up / failure)."""
        while not self._q.empty():
            try: self._q.get_nowait()
            except queue.Empty: break

    def stop(self):
        """Kill audio immediately: drain queue, stop worker, terminate aplay."""
        # 1. Drain buffered PCM so the worker writes nothing more.
        self.clear()
        # 2. Signal the worker loop to exit.
        try: self._q.put_nowait(None)
        except Exception: pass
        # 3. Kill aplay hard so its internal buffer never plays out.
        proc = self._proc
        if proc is not None:
            try: proc.terminate()
            except Exception: pass
            try: proc.wait(timeout=1.0)
            except Exception: pass
        # 4. Wait for the worker thread to finish so no audio escapes after return.
        if self._th.is_alive():
            self._th.join(timeout=2.0)

    def silence(self):
        """
        Phase-1 shutdown: stop all audio output immediately without touching
        the aplay process.  Call this while curses is still active (no SIGCHLD
        risk).  Follow up with stop() once curses has finished its final getch().
        Draining the queue + closing stdin causes aplay to exit cleanly on its
        own within ~40 ms -- well before the terminal prompt reappears.
        """
        self.clear()
        try: self._q.put_nowait(None)
        except Exception: pass


# ─────────────────────────────────────────────────────────────────────────────
# SHARED STATE
# ─────────────────────────────────────────────────────────────────────────────

@dataclasses.dataclass
class ModemState:
    name:   str  = ""
    status: str  = "IDLE"
    wave:   str  = "IDLE"   # IDLE DTMF NOISE SWEEP CARRIER STATIC
    log:    list = dataclasses.field(default_factory=list)

class UIState:
    def __init__(self, profile: ModemProfile, fail_prob: float,
                 isp_number: str = "555-0199", isp_label: str = "dialin.local",
                 debug: bool = False, max_attempts: int = 4,
                 scenario_weights: Optional[List[float]] = None,
                 sound_scheme_idx: int = 0,
                 ml_count: int = 1, ml_mode: int = 0):
        self.lock          = threading.Lock()
        self.customer      = ModemState(name=profile.name)
        self.isp           = ModemState(name=f"ISP  --  {isp_label}  (V.90 server)")
        self.line_state    = "IDLE"
        self.progress      = 0.0
        self.phase_lbl     = ""
        self.phase_desc    = ""
        self.signal        = 0
        self.rx            = 0
        self.tx            = 0
        self.snr           = 0
        self.final_speed   = ""
        self.ip_c          = "10.0.0.2"
        self.ip_s          = "10.0.0.1"
        self.quit          = False
        self.done          = False
        self.profile       = profile
        self.fail_prob     = fail_prob
        self.attempt       = 1
        self.max_attempts  = max_attempts
        self.bytes_rx      = 0
        self.bytes_tx      = 0
        self.ping_ms       = 0
        self.online_lines  : list = []
        self.vol_flash     = 0   # frames to flash volume bar after change
        self.isp_number    = isp_number
        self.isp_label     = isp_label
        self.debug             = debug
        self.scenario_weights  = scenario_weights   # per-scenario failure weights
        self.sound_scheme_idx  = sound_scheme_idx
        self.ml_count          = ml_count            # total modems (1=no MLPPP)
        self.ml_mode           = ml_mode             # 0=simultaneous 1=serial
        self.ml_connected      = 0                   # modems currently online
        self.ml_total_speed    = 0                   # aggregate bps
        # debug stats (updated each phase)
        # page-load simulation state
        self.page_load_active   : bool  = False
        self.page_load_url      : str   = ''
        self.page_load_stage    : str   = ''
        self.page_load_progress : float = 0.0
        self.page_load_bytes    : int   = 0
        self.page_load_total    : int   = 0
        # per-link MLPPP status (list of dicts)
        self.ml_links           : list  = []
        # overlay control  (None / 'C' / 'I')
        self.overlay            : Optional[str] = None
        self.overlay_sel        : int   = 0
        # modem speaker relay (false = muted path — line still “active” in sim)
        self.speaker_enabled        : bool = True
        # ISP-side noise injection (mixed in _apply_playback_fx)
        self.isp_upstream_noise    : bool = False
        # effective ceiling on aggregate data rate (bps); None = no ISP cap
        self.throttle_bps          : Optional[int] = None
        # extra RTT from traffic shaping (ms), applied in online + page load
        self.extra_latency_ms      : int = 0
        # modal dialog (blocking error / info / choice)
        self.modal_title           : Optional[str] = None
        self.modal_message         : Optional[str] = None
        self.modal_kind            : Optional[str] = None  # None/info/choice
        self.modal_options         : list = []              # list[(id,label)]
        self.modal_sel             : int = 0
        self.modal_context         : Optional[str] = None  # handler tag for choice modals
        # set True from overlay to abort in-progress dial (ATH / ATZ / NAS)
        self.dial_abort            : bool = False
        # phone pickup joke: effective pipe multiplier over time (ONLINE only)
        # mode: None / 'ALLOW' (drop to 0 and stay) / 'RECOVER' (drop then return)
        self.phone_pickup_mode          : Optional[str] = None
        self.phone_pickup_start_ts      : float = 0.0
        self.phone_pickup_disconnected  : bool  = False  # True once ALLOW triggers disconnect
        # one-shot: play V.34-ish retrain swoosh in online loop
        self.pending_retrainFX     : bool = False
        # line-quality injection (from overlay)
        self.inject_noise           : bool = False
        self.inject_disconnect      : bool = False
        self.inject_forced_reason   : str  = ""   # action tag from overlay
        self.forced_disconnect_done : bool = False  # True = skip _natural_hangup
        # debug stats (updated each phase)
        self.dbg_phase_dur : float = 0.0
        self.dbg_freqs     : str   = ""
        self.dbg_fm        : float = 0.0
        self.dbg_nm        : float = 0.0
        # ISP "fun" rip-off sim (throughput factor + customer pushback)
        self.isp_ripoff_mult          : float = 1.0
        self.cust_fightback           : float = 0.0
        self.isp_dns_hijack           : bool = False
        self.isp_ad_inject            : bool = False
        self.isp_surge_billing        : bool = False
        self.isp_billing_tick         : int = 0
        self.demo_disk_redial_pending : bool = False
        self.request_session_redial    : bool = False

_state : UIState
_audio : AudioPlayer

# ─────────────────────────────────────────────────────────────────────────────
# SEQUENCER  --  runs in a background thread
# Audio and text are synchronised: log messages fire at the moment sound plays.
# ─────────────────────────────────────────────────────────────────────────────

def _wait(s: float):
    steps = max(1, int(s/0.04))
    for _ in range(steps):
        if _state.quit:
            return
        with _state.lock:
            if _state.dial_abort:
                raise DialAbort()
        time.sleep(0.04)

def _clog(text: str, tag: str = "AT"):
    with _state.lock: _state.customer.log.append((text, tag))

def _ilog(text: str, tag: str = "AT"):
    with _state.lock: _state.isp.log.append((text, tag))

def _wave(side: str, w: str):
    with _state.lock:
        if side == 'C': _state.customer.wave = w
        else:           _state.isp.wave      = w

def _stats(sig: int, rx: int, tx: int, snr: int):
    with _state.lock:
        _state.signal = sig; _state.rx = rx
        _state.tx     = tx;  _state.snr = snr

def _set_ls(s: str):
    with _state.lock: _state.line_state = s

def _set_phase(prog: float, lbl: str, desc: str):
    with _state.lock:
        _state.progress   = prog
        _state.phase_lbl  = lbl
        _state.phase_desc = desc

# ── Synchronised audio+text primitive ────────────────────────────────────────
#
# THE SYNC CONTRACT
# -----------------
# Every audible event goes through _sync().  It:
#   1. Drains whatever is left in the audio queue (so the new sound starts
#      immediately, never after a queued tail from the previous step).
#   2. Logs text for both sides at the same instant as audio is queued.
#   3. Waits exactly len(buf)/SR seconds -- the true playback duration of
#      the buffer -- before returning.  This guarantees the next event's
#      text+sound fire only after this one has finished playing.
#
# The aplay buffer is now 40 ms (down from 500 ms), so the gap between
# "queued" and "actually heard" is imperceptible (~40 ms).
#
# Pure pauses (no audio) use _gap(seconds).
# ─────────────────────────────────────────────────────────────────────────────

def _sync(buf: List[int],
          ctext: str = "", ctag: str = "AT",
          itext: str = "", itag: str = "AT") -> None:
    """
    Drain queue, log text, play audio, wait exact buffer duration.
    Text appears at the same moment the sound starts; nothing else runs until
    the sound finishes.
    """
    if _state.quit:
        return
    with _state.lock:
        if _state.dial_abort:
            raise DialAbort()
    _audio.clear()                       # remove any leftover audio
    if ctext: _clog(ctext, ctag)         # log text NOW (same moment as sound)
    if itext: _ilog(itext, itag)
    _audio.play(buf)                     # queue audio (starts within ~40 ms)
    _wait(len(buf) / SR)                 # wait exactly the buffer's duration


def _gap(s: float) -> None:
    """Silent pause between events (no audio, no log)."""
    if not _state.quit:
        _wait(s)


def _handle_dial_abort() -> None:
    """User cancelled setup from the control panel — clean up and end the session."""
    _audio.clear()
    _wave("C", "IDLE")
    _wave("I", "IDLE")
    _clog("NO CARRIER  (aborted during dial)", "RING")
    _ilog("Call setup aborted  (operator / client command)", "SYS")
    with _state.lock:
        _state.dial_abort = False
        _state.customer.status = "DISCONNECTED  (aborted)"
        _state.isp.status = "IDLE  --  awaiting next call"
        _state.line_state = "FAILED"
        _state.done = True


def _dtmf_digit(ch: str) -> None:
    """Play one DTMF digit without draining -- digits flow continuously."""
    if _state.quit:
        return
    with _state.lock:
        if _state.dial_abort:
            raise DialAbort()
    buf = silence(0.18) if ch == '-' else dtmf(ch)
    _audio.play(buf)
    _wait(len(buf) / SR)


_AT_CMDS = [
    ("ATZ",                   "OK",  0.28),
    ("ATE0Q0V1",              "OK",  0.18),
    ("AT+MS=V90,1,300,56000", "OK",  0.22),
    ("AT%C1\\N5",             "OK",  0.20),
    ("AT&K3 M1L3",            "OK",  0.20),
    ("AT+FCLASS=0",           "OK",  0.15),
]



_ISDN_AT_CMDS = [
    ("ATZ",                    "OK",  0.15),
    ("AT+FCLASS=0",            "OK",  0.10),
    ("AT+CBST=116,0,1",        "OK",  0.12),   # ISDN data bearer
    ("AT+ISDN=1",              "OK",  0.10),
    ("AT&D2 &C1",              "OK",  0.10),
]


def _do_single_attempt_isdn() -> bool:
    """
    ISDN connect sequence: no analog hiss, no CED/ANSam, no FSK flags.
    D-channel Q.931 signaling -> B-channel activation -> PPP in < 2 s.
    """
    p = _state.profile

    _wave('C','IDLE'); _wave('I','IDLE')
    _sync(speaker_click(0.20), "ISDN TA initialising  --  D-channel up", "SYS")
    _sync(isdn_dial_tone(0.18), "ISDN dial tone  (425 Hz)", "SYS")

    for cmd, resp, delay in _ISDN_AT_CMDS:
        if _state.quit: return False
        _clog(f"--> {cmd}", "AT")
        _gap(delay * 0.3)
        _clog(f"<-- {resp}", "OK")
        _gap(delay * 0.7)

    # Dial via ISDN
    if _state.quit: return False
    dial_num = _state.isp_number
    with _state.lock:
        _state.customer.status = "DIALLING  (ISDN)"
        _state.line_state      = "DIALLING"
    _wave('C','DTMF'); _wave('I','IDLE')
    first_buf = dtmf(dial_num[0]) if dial_num[0] != '-' else silence(0.15)
    _sync(first_buf, f"--> ATDT {dial_num}  [ISDN]", "AT")
    for ch in dial_num[1:]:
        _dtmf_digit(ch)

    # ISDN ringback (1 cycle, shorter than analog)
    if _state.quit: return False
    with _state.lock:
        _state.customer.status = "RINGING  (ISDN)"
        _state.line_state      = "RINGING"
    _sync(isdn_progress_tone(1),
          "<-- ALERTING  (Q.931)", "RING",
          "Q.931 ALERTING sent", "RING")

    # ISDN connect -- no CED/ANSam, straight to B-channel activation
    if _state.quit: return False
    with _state.lock:
        _state.isp.status      = "ANSWERING  --  Q.931 CONNECT"
        _state.customer.status = "ISDN CONNECT  --  B-channel up"
        _state.line_state      = "NEGOTIATING"
    _set_ls("NEGOTIATING")
    _sync(isdn_connect_confirm(),
          "[ISDN] Q.931 CONNECT  --  B-channel activating", "NEG",
          "[ISDN] Q.931 CONNECT sent  --  B-channel open", "OK")

    # Phase loop (D-channel + PPP, very fast)
    n_phases = len(p.phases)
    with _state.lock:
        _state.customer.status = "NEGOTIATING  (ISDN)"
        _state.isp.status      = "NEGOTIATING  (ISDN)"

    for idx, (phase_lbl, freqs, fm, nm, base_dur) in enumerate(p.phases):
        if _state.quit: return False
        frac = (idx + 1) / n_phases
        _set_phase(frac, f"[{idx+1}/{n_phases}]", phase_lbl)

        # Failure injection (middle phases only)
        if 2 <= idx <= n_phases - 3 and _state.fail_prob > 0:
            n_pool    = max(1, n_phases - 4)
            per_phase = 1.0 if _state.fail_prob > 1.0 else _state.fail_prob / n_pool
            if random.random() < per_phase:
                _do_failure(idx, n_phases,
                            weights=getattr(_state, 'scenario_weights', None))
                return False

        _wave('C', 'CARRIER'); _wave('I', 'CARRIER')
        audio_buf = isdn_bchan_activate()
        with _state.lock:
            _state.dbg_phase_dur = len(audio_buf) / SR
            _state.dbg_freqs     = f"{freqs[0]}Hz"
            _state.dbg_fm        = fm
            _state.dbg_nm        = nm
        _sync(audio_buf,
              f"[ISDN] {phase_lbl}", "NEG",
              f"[ISDN] {phase_lbl}", "NEG")
        jitter = random.randint(-2, 2)
        _stats(max(0, min(100, int(frac*96) + jitter)),
               max(0, min(100, int(frac*98) + jitter)),
               max(0, min(100, int(frac*97) + jitter)),
               max(0, min(60,  int(frac*59) + jitter // 2)))

    # CONNECT
    if _state.quit: return False
    _set_phase(1.0, "CONNECT", "ISDN B-channel locked")
    _wave('C','CARRIER'); _wave('I','CARRIER')
    _sync(isdn_connect_confirm())
    speed = p.max_speed
    _stats(98, 99, 98, 59)
    with _state.lock:
        _state.final_speed     = speed
        _state.customer.status = f"ONLINE  (ISDN  {speed} bps)"
        _state.isp.status      = f"ONLINE  (ISDN  {speed} bps)"
        _state.line_state      = "ONLINE"
    _clog("", "")
    _clog(f"CONNECT {speed}  ISDN  {p.compression}", "OK")
    _clog(f"IP : {_state.ip_c}   GW : {_state.ip_s}", "SYS")
    _clog("PPP session active  (ISDN).", "SYS")
    _ilog("", "")
    _ilog(f"CONNECT {speed}  ISDN  {p.compression}", "OK")
    _ilog(f"Assigned {_state.ip_c}  to ISDN client", "SYS")
    return True


def _do_single_attempt() -> bool:
    """
    Run one full dial/negotiate sequence.
    Dispatches to ISDN variant automatically for ISDN profiles.
    Returns True  if connection was established (user stays online).
    Returns False if a handshake failure occurred and redial is needed.
    """
    p = _state.profile
    if getattr(p, 'is_isdn', False):
        return _do_single_attempt_isdn()

    # ── 1. Speaker relay click + dial tone ───────────────────────────────────
    _wave('C','IDLE'); _wave('I','IDLE')
    _sync(speaker_click(0.28), "Modem initialising  --  speaker ON", "SYS")
    _sync(dial_tone(0.40),     "Dial tone  (350 + 440 Hz)", "SYS")

    for cmd, resp, delay in _AT_CMDS:
        if _state.quit: return False
        _clog(f"--> {cmd}", "AT")
        _gap(delay * 0.35)
        _clog(f"<-- {resp}", "OK")
        _gap(delay * 0.65)

    # Hayes: brief clean 1800 Hz probe before dialling
    if p.init_fn is not None and not _state.quit:
        _sync(p.init_fn(), "Modem line probe  (1800 Hz)", "NEG")

    # ── 2. Dial ──────────────────────────────────────────────────────────────
    if _state.quit: return False
    dial_num = _state.isp_number
    dial_cmd = f"ATDT {dial_num}"
    with _state.lock:
        _state.customer.status = "DIALLING"
        _state.line_state      = "DIALLING"
    _wave('C','DTMF'); _wave('I','IDLE')
    # Tight coupling: the ATDT log entry fires exactly when the first tone
    # plays.  _sync drains any leftover audio so the first digit starts from
    # a clean baseline with no aplay buffer carry-over from previous steps.
    first_digit = dial_num[0]
    first_buf   = silence(0.18) if first_digit == '-' else dtmf(first_digit)
    _sync(first_buf, f"--> {dial_cmd}", "AT")
    for ch in dial_num[1:]:
        _dtmf_digit(ch)

    # ── 3. Ringback ───────────────────────────────────────────────────────────
    if _state.quit: return False
    with _state.lock:
        _state.customer.status = "RINGING  --  awaiting answer"
        _state.customer.wave   = "IDLE"
        _state.line_state      = "RINGING"

    for ring_n in range(1, 3):
        if _state.quit: return False
        with _state.lock: _state.isp.status = f"RINGING  ({ring_n})"
        _wave('I','NOISE')
        ring_buf = ringback(1)   # 2 s ring + 3.5 s gap
        # Log both sides exactly when the ring sound starts
        _sync(ring_buf,
              f"<-- RINGING  ({ring_n})", "RING",
              f"RING  {ring_n}", "RING")
        # Occasional line-noise burst between rings (no log, just atmosphere)
        if random.random() < 0.40:
            _sync(line_noise_burst(0.10, 0.12))

    # ── 4. ISP answers -- CED ────────────────────────────────────────────────
    if _state.quit: return False
    with _state.lock:
        _state.isp.status      = "ANSWERING  --  CED 2100 Hz"
        _state.customer.status = "CARRIER DETECTED  --  2100 Hz"
    _wave('C','NOISE'); _wave('I','NOISE')
    _set_ls("NEGOTIATING")
    _sync(ced_tone(3.3),
          "<-- CARRIER  2100 Hz  (CED -- echo suppressor disabled)", "RING",
          "--> ATA  --  sending CED  2100 Hz  (ITU-T V.25)", "OK")

    # ── 5. ANSam ─────────────────────────────────────────────────────────────
    if _state.quit: return False
    with _state.lock:
        _state.isp.status = "ANSam  --  15 Hz AM modulated carrier"
    _sync(ansam(0.80),
          "[V.8] ANSam received  --  15 Hz AM  (V.8 capable server)", "NEG",
          "[V.8] Sending ANSam  --  15 Hz AM modulation", "OK")

    # ── 6. USR bong ──────────────────────────────────────────────────────────
    if p.has_bong and not _state.quit:
        _sync(usr_bong(),
              "[USR] 3-note ID chord  (Sportster signature)", "NEG",
              "[USR] ID chord received  --  USRobotics client detected", "NEG")

    # ── 7. V.21 FSK flags ────────────────────────────────────────────────────
    if _state.quit: return False
    _wave('C','NOISE'); _wave('I','NOISE')
    fsk1 = v21_fsk(1, 0.55*p.timing_mult, p.noise_floor)
    _sync(fsk1,
          "[V.21] Originating  Ch1  (mark=1080 Hz  space=980 Hz)", "NEG",
          "[V.21] Receiving Ch1  --  preparing Ch2 answer flags", "NEG")
    fsk2 = v21_fsk(2, 0.45*p.timing_mult, p.noise_floor*0.6)
    _sync(fsk2,
          "[V.21] Receiving Ch2 answer  (mark=1650 Hz  space=1750 Hz)", "NEG",
          "[V.21] Sending Ch2  (mark=1650 Hz  space=1750 Hz)", "NEG")

    # ── 8. V.34/V.90 negotiation phases ──────────────────────────────────────
    if _state.quit: return False
    n_phases = len(p.phases)
    with _state.lock:
        _state.customer.status = "NEGOTIATING"
        _state.isp.status      = "NEGOTIATING"

    for idx, (phase_lbl, freqs, fm, nm, base_dur) in enumerate(p.phases):
        if _state.quit: return False

        frac = (idx+1) / n_phases
        _set_phase(frac, f"[{idx+1}/{n_phases}]", phase_lbl)

        # Failure injection (not in first 2 or last 2 phases)
        if 2 <= idx <= n_phases-3 and _state.fail_prob > 0:
            n_pool    = max(1, n_phases - 4)
            per_phase = 1.0 if _state.fail_prob > 1.0 else _state.fail_prob / n_pool
            if random.random() < per_phase:
                _do_failure(idx, n_phases,
                            weights=getattr(_state, 'scenario_weights', None))
                return False

        # Waveform style
        if frac < 0.45:   _wave('C','NOISE');   _wave('I','NOISE')
        elif frac < 0.78: _wave('C','SWEEP');   _wave('I','SWEEP')
        else:             _wave('C','CARRIER'); _wave('I','CARRIER')

        # Generate audio then sync (text fires exactly when audio starts)
        if 3 <= idx <= 5 and idx % 2 == 0:
            audio_buf = sweep_audio(p)
        else:
            audio_buf = phase_audio(p, idx)

        # Update debug stats before playing so they're visible immediately
        with _state.lock:
            _state.dbg_phase_dur = len(audio_buf) / SR
            _state.dbg_freqs     = f"{freqs[0]}+{freqs[1]}Hz" if len(freqs) >= 2 \
                                   else f"{freqs[0]}Hz" if freqs else "—"
            _state.dbg_fm        = fm
            _state.dbg_nm        = nm

        _sync(audio_buf,
              f"[{p.short}] {phase_lbl}", "NEG",
              f"[{p.short}] {phase_lbl}", "NEG")

        jitter = random.randint(-4, 4)
        _stats(
            max(0, min(100, int(frac*82) + jitter)),
            max(0, min(100, int(frac*91) + jitter)),
            max(0, min(100, int(frac*87) + jitter)),
            max(0, min(60,  int(frac*55) + jitter//2)),
        )

    # ── 9. Motorola: connect chirp just before CONNECT ───────────────────────
    if p.carrier_freq >= 1900 and p.carrier_jitter == 0.0 and not _state.quit:
        _sync(moto_connect_chirp(), "[Moto] Fast-connect chirp", "NEG")

    # ── 10. Carrier lock / CONNECT ───────────────────────────────────────────
    if _state.quit: return False
    _set_phase(1.0, "CONNECT", "Rate confirmed")
    _wave('C','CARRIER'); _wave('I','CARRIER')
    _sync(carrier_hum(p.carrier_freq, 0.6, p.carrier_amp, p.carrier_jitter))

    speed = p.max_speed
    _stats(95, 98, 93, 58)

    with _state.lock:
        _state.final_speed     = speed
        _state.customer.status = f"ONLINE  --  {speed} bps"
        _state.isp.status      = f"ONLINE  --  {speed} bps"
        _state.line_state      = "ONLINE"

    _clog("", "")
    _clog(f"CONNECT {speed}  V.90  {p.compression}  MNP5", "OK")
    _clog(f"IP : {_state.ip_c}   GW : {_state.ip_s}", "SYS")
    _clog("PPP session active.", "SYS")
    _ilog("", "")
    _ilog(f"CONNECT {speed}  V.90  {p.compression}", "OK")
    _ilog(f"Assigned {_state.ip_c}  to client", "SYS")
    _ilog("Session active.", "SYS")
    return True   # connected


# ── Fake HTTP activity for the online display ────────────────────────────────
_FAKE_SITES = [
    "GET / HTTP/1.1  host: altavista.com",
    "GET /images/logo.gif  host: yahoo.com",
    "GET /news/index.html  host: cnn.com",
    "SMTP  250 OK  mail from:user@aol.com",
    "GET /search?q=linux  host: excite.com",
    "FTP DATA  transfer: 4096 bytes",
    "GET /mp3/track01.mp3  --  429 Too Many Requests",
    "GET /chat/room.cgi  host: icq.com",
    "POP3  +OK  3 messages  14822 octets",
    "GET /weather/bucharest  host: weather.com",
    "GET /download/winamp.exe  host: winamp.com",
    "IRC  PRIVMSG #linux  :hello world",
    "GET /hotmail/inbox  host: hotmail.com",
    "DNS  query: www.geocities.com  --  A  192.168.1.1",
    "NNTP  GROUP  rec.humor.funny  --  241 9832 art",
    "GET /cgi-bin/counter.cgi  host: angelfire.com",
    "AIM  OSCAR  SNAC  0x04  buddy online: UrSoCool99",
    "GET /download/ie5setup.exe  --  206 Partial Content",
    "TELNET  220 freeshell.org  FTP ready",
]

_HIJACK_FAKE = [
    "GET /portal  host: we-absolutely-arent-your-isp.net  [HIJACK]",
    "GET /speedtest  redirected -> isp-ad-network.com/track  [DNS]",
    "DNS  A  www.google.com  ->  10.66.6.6  (ISP 'helper')",
]

_ISP_AD_LINES = [
    "POPUP  Subscribe to GOLD 56k  --  only $19.99/mo  (auto-enroll)",
    "INSERT  DOUBLE-CLICK TO WIN  --  you've been selected!!!",
    "BANNER  You've used 47 of your 30 'fair' megabytes today",
]

# ── Per-action messages for overlay-triggered forced disconnects ─────────────
_FORCED_DISC_INFO = {
    'force_disconnect': (
        "--> ATH0  --  modem off-hook (manual hangup)",          "AT",
        "Remote: carrier loss  --  TCP/IP teardown",             "SYS",
        "<-- NO CARRIER  (ATH0 by user)",                        "RING",
        "Client disconnected cleanly  --  port freed",           "SYS",
        "NO CARRIER  (ATH0)", "RESET  --  client disconnected",
    ),
    'isp_disconnect': (
        "<-- FORCE DISCONNECT  --  ISP NAS dropped session",     "FAIL",
        "--> Force-disconnecting client  (admin command)",        "FAIL",
        "<-- NO CARRIER  (ISP NAS dropped call)",                "RING",
        "Session terminated.  Port freed.",                      "SYS",
        "NO CARRIER  (ISP dropped)", "FORCE DISCONNECT  --  session ended",
    ),
    'isp_reset_port': (
        "<-- RESET  --  NAS port reset by ISP",                  "FAIL",
        "--> NAS port reset  (maintenance / port cycling)",       "FAIL",
        "<-- NO CARRIER  (NAS port reset)",                      "RING",
        "Port recycled.  Awaiting next client.",                  "SYS",
        "NO CARRIER  (NAS reset)", "PORT RESET  --  recycled",
    ),
    'reset_at': (
        "--> ATZ  --  modem AT register reset",                   "AT",
        "Remote: unexpected carrier loss",                        "SYS",
        "<-- NO CARRIER  (AT register reset)",                   "RING",
        "Client unexpectedly dropped  --  port freed",           "SYS",
        "NO CARRIER  (ATZ reset)", "RESET  --  unexpected drop",
    ),
}


def _forced_disconnect_sequence(reason: str) -> None:
    """
    Play a dramatic forced-disconnect audio+log sequence for each overlay
    action.  Called from _online_loop when inject_forced_reason is set.
    Never called when the user just presses Q (that uses _natural_hangup).
    """
    info = _FORCED_DISC_INFO.get(reason, _FORCED_DISC_INFO['force_disconnect'])
    cm1, ct1, im1, it1, cm2, ct2, im2, it2, cst, ist = info

    _wave('C', 'STATIC'); _wave('I', 'STATIC')
    _stats(0, 0, 0, 0)

    p = _state.profile

    if reason in ('isp_disconnect', 'isp_reset_port'):
        # ISP side initiates: rising noise swamps carrier, then hard cut
        _sync(_noise_fail_audio(), cm1, ct1, im1, it1)
        _gap(0.20)
        _sync(_remote_hangup_audio(), cm2, ct2, im2, it2)

    elif reason == 'reset_at':
        # AT register reset: relay click -> static burst -> crackle
        click_static = speaker_click(0.38) + line_noise_burst(0.10, 0.55) + disconnect_crackle()
        _sync(click_static, cm1, ct1, im1, it1)
        _gap(0.14)
        _sync(silence(0.05), cm2, ct2, im2, it2)

    else:  # force_disconnect (default): customer ATH0 -- carrier fade then click
        n = int(SR * 0.28)
        ph = 0.0; fade = []
        for i in range(n):
            amp_f = int(AMP * p.carrier_amp * (1.0 - i / n) * 0.85)
            ph += 2 * math.pi * p.carrier_freq / SR
            fade.append(int(amp_f * math.sin(ph)))
        _sync(fade + line_noise_burst(0.07, 0.38), cm1, ct1, im1, it1)
        _gap(0.12)
        _sync(speaker_click(0.30) + disconnect_crackle(), cm2, ct2, im2, it2)

    with _state.lock:
        _state.customer.status      = cst
        _state.isp.status           = ist
        _state.line_state           = "FAILED"
        _state.forced_disconnect_done = True
    _gap(1.2)


def _demo_disk_swap_sequence() -> None:
    """
    Floppy eject / insert theatre — NO CARRIER — schedule another full dial
    without ending the whole emulator session.
    """
    p = _state.profile
    _wave("C", "STATIC")
    _wave("I", "STATIC")
    _stats(0, 0, 0, 0)
    _sync(
        floppy_disk_eject_sound(),
        "[DISK] DOS: ejecting A:  INSTALL.DSK  (motor off)", "SYS",
        "[NAS] client removable media — session I/O stalled", "SYS",
    )
    _gap(0.12)
    _sync(
        floppy_disk_insert_sound(),
        "[DISK] inserting B:  BONUS_DEMO.DSK  (spin-up)", "SYS",
        "[NAS] new volume — expecting fresh PPP train", "SYS",
    )
    n = int(SR * 0.22)
    ph = 0.0
    fade: List[int] = []
    for i in range(n):
        amp_f = int(AMP * p.carrier_amp * (1.0 - i / n) * 0.75)
        ph += 2 * math.pi * p.carrier_freq / SR
        fade.append(int(amp_f * math.sin(ph)))
    _sync(
        fade + disconnect_crackle(),
        "<-- NO CARRIER  (media change / stack reset)", "RING",
        "Link dropped: demo disk swap (operator fiction)", "SYS",
    )
    with _state.lock:
        _state.page_load_active = False
        _state.customer.status = "NO CARRIER  (demo disk swap)"
        _state.isp.status = "IDLE  --  awaiting re-dial"
        _state.line_state = "REDIAL"
        _state.request_session_redial = True


def _online_loop():
    """Runs while connected.  Simulates data transfer + plays carrier audio."""
    _wave('C','CARRIER'); _wave('I','CARRIER')
    p     = _state.profile
    t0    = time.time()
    last  = time.time()
    with _state.lock:
        _state.isp_billing_tick = 0
    while not _state.quit:
        now   = time.time()
        dt    = now - last
        last  = now
        pickup_factor = 1.0
        with _state.lock:
            agg = _state.ml_total_speed
            cap = _state.throttle_bps
            lat = _state.extra_latency_ms
            do_retrain = _state.pending_retrainFX
            if do_retrain:
                _state.pending_retrainFX = False
            rip = _state.isp_ripoff_mult
            fbk = _state.cust_fightback
            hij = _state.isp_dns_hijack
            ads = _state.isp_ad_inject
            sur = _state.isp_surge_billing
            _state.isp_billing_tick += 1
            bill_n = _state.isp_billing_tick

            # Phone pickup joke: degrade throughput and carrier while active.
            if _state.phone_pickup_mode:
                elapsed = now - _state.phone_pickup_start_ts
                if _state.phone_pickup_mode == "ALLOW":
                    pickup_factor = max(0.0, 1.0 - elapsed / 2.2)
                    # Once quality is fully gone, drop the connection offline.
                    if pickup_factor == 0.0 and not _state.phone_pickup_disconnected:
                        _state.phone_pickup_disconnected = True
                        _state.inject_disconnect = True
                        _state.inject_forced_reason = "phone_pickup_allow"
                else:  # "RECOVER"
                    if elapsed < 2.0:
                        pickup_factor = 1.0 - elapsed / 2.0
                    elif elapsed < 2.5:
                        pickup_factor = 0.0
                    else:
                        pickup_factor = min(1.0, (elapsed - 2.5) / 3.0)
                    if pickup_factor >= 0.999:
                        _state.phone_pickup_mode = None
                        pickup_factor = 1.0

                # Update visual meters while the interference happens.
                _state.signal = int(95 * pickup_factor)
                _state.rx = int(100 * pickup_factor)
                _state.tx = int(100 * pickup_factor)
                _state.snr = int(60 * pickup_factor)
        pipe_eff = max(0.22, min(1.0, float(rip) + float(fbk)))
        base = agg if agg > 0 else _profile_speed_bps(p)
        speed = min(base, cap) if cap else base
        speed = max(1200, int(speed))
        # Bytes accrued at ~65% link utilisation (then ISP fine-print shrink)
        rx_inc = int(speed * 0.065 * dt * pipe_eff * pickup_factor)
        tx_inc = int(speed * 0.018 * dt * pipe_eff * pickup_factor)
        with _state.lock:
            _state.bytes_rx += rx_inc
            _state.bytes_tx += tx_inc
            _state.ping_ms   = random.randint(120, 380) + lat
            if sur and bill_n % 5 == 0:
                fee = random.randint(2, 11)
                _state.isp.log.append(
                    (f"[BILLING] surge interval  +${fee}.99  'regulatory' line item",
                     "FAIL"))
                _state.customer.log.append(
                    ("!!! SURGE PRICING: check the fine print you never read", "FAIL"))
            if random.random() < 0.08:
                if ads and random.random() < 0.38:
                    extra = random.choice(_ISP_AD_LINES) + f"  [{random.randint(20,120)}ms]"
                elif hij and random.random() < 0.35:
                    extra = random.choice(_HIJACK_FAKE) + f"  [{random.randint(15,90)}ms]"
                else:
                    extra = (random.choice(_FAKE_SITES)
                             + f"  [{random.randint(1,80)}ms]")
                _state.online_lines.append(extra)
                if len(_state.online_lines) > 40:
                    _state.online_lines = _state.online_lines[-40:]
        if do_retrain:
            _clog("[V.34] Line retrain  (+MS)  --  probe burst", "NEG")
            _ilog("[V.34] Accepting client retrain request", "SYS")
            try:
                sw = sweep_audio(p)
                n  = min(len(sw), int(SR * 0.42))
                _audio.play(sw[:n])
            except Exception:
                _audio.play(handshake_burst(
                    [1600, 2400, 3000], 0.28, 0.02, 0.10, p.noise_floor * _scheme_noise_mult))
        # Carrier hum (plus noise injection if requested from overlay)
        carrier_amp = p.carrier_amp * pickup_factor
        _audio.play(carrier_hum(p.carrier_freq, 0.5, carrier_amp, p.carrier_jitter * _scheme_jitter_mult))
        if pickup_factor < 0.15 and random.random() < 0.04:
            _audio.play(pop_static(0.16))
        if p.noise_floor > 0.20 and random.random() < 0.05:
            _audio.play(pop_static(0.15))
        if getattr(_state, 'inject_noise', False):
            _audio.play(line_noise_burst(0.15, 0.45))
        demo_swap = False
        with _state.lock:
            if _state.demo_disk_redial_pending:
                _state.demo_disk_redial_pending = False
                demo_swap = True
        if demo_swap:
            _demo_disk_swap_sequence()
            break
        if getattr(_state, 'inject_disconnect', False):
            reason = _state.inject_forced_reason
            with _state.lock:
                _state.inject_disconnect    = False
                _state.inject_forced_reason = ""
            if reason:
                _forced_disconnect_sequence(reason)
            break
        _wait(0.5)


def _mlppp_bundle_negotiation(n: int) -> None:
    """
    After every physical link trains, run a short synthetic MLPPP LCP / IPCP
    exchange (tones + logs).  Mirrors real MP+ bundle bring-up.
    """
    if n <= 1 or _state.quit:
        return
    p = _state.profile
    _gap(0.06)
    if _state.quit:
        return
    _sync(
        handshake_burst([2048, 3072, 3584], 0.22 * p.timing_mult,
                        0.007, 0.07, p.noise_floor * _scheme_noise_mult),
        "[MLPPP] LCP  MRRU + Endpoint Discriminator  (bundle ID)", "NEG",
        "[MLPPP] LCP  Conf-Ack  --  multilink class 2", "NEG",
    )
    _sync(
        handshake_burst([2048, 2400], 0.17 * p.timing_mult,
                        0.006, 0.055, p.noise_floor * _scheme_noise_mult * 0.9),
        "[MLPPP] IPCP  one NCP for the bundle  (no IPCP per link)", "NEG",
        "[MLPPP] IPCP  Conf-Ack  --  gateway on mlp0", "NEG",
    )
    with _state.lock:
        tot = _state.ml_total_speed
    _clog(f"MLPPP: bundle IPCP complete  --  {n} links  {tot} bps aggregate", "OK")
    _ilog("MLPPP: Virtual iface up  --  WRR fragmenter / reassembly enabled", "SYS")


def _mlppp_connect():
    """
    Multi-link PPP bonding.

    Simultaneous (Win XP): ALL N modems start dialling at the same time.
      Each runs its own full handshake in a daemon thread.  The audio queue
      serialises sound naturally; per-link status is tracked in ml_links[].
      The first modem's thread also drives the CED/ANSam sequence; others
      start from ringback onward to avoid identical duplicate audio.

    Serial (Win ME): modems bond one at a time; each completes before the next.
    """
    p = _state.profile
    n = _state.ml_count

    # Initialise per-link status list
    with _state.lock:
        _state.ml_links       = [{"n": k, "status": "IDLE", "speed": 0} for k in range(1, n+1)]
        _state.ml_connected   = 0
        _state.ml_total_speed = 0

    link_bps = _profile_speed_bps(p)

    if n <= 1:
        # Single modem -- link 1 is already connected via _do_single_attempt
        with _state.lock:
            _state.ml_connected   = 1
            _state.ml_total_speed = link_bps
            _state.ml_links[0]["status"] = "ONLINE"
            _state.ml_links[0]["speed"]  = link_bps
        _online_loop()
        return

    mode_lbl = "simultaneous" if _state.ml_mode == 0 else "serial"
    _clog(f"MLPPP: {n} modems  ({mode_lbl}  bonding)", "SYS")
    _ilog(f"MLPPP: {n}-link aggregate  ({mode_lbl})", "SYS")

    ml_thread_abort = threading.Event()

    # ── per-link handshake (full for link 1, abbreviated for 2..N) ───────────
    def _link_handshake(k: int):
        """Run handshake for link k (1-based).  Thread-safe; serialises audio."""
        lk = k - 1   # 0-based index into ml_links

        def _pulse_abort():
            with _state.lock:
                if _state.dial_abort:
                    raise DialAbort()

        def _set_link(status, speed=0):
            with _state.lock:
                _state.ml_links[lk]["status"] = status
                if speed:
                    _state.ml_links[lk]["speed"] = speed

        _set_link("DIALLING")
        if _state.quit:
            return
        _pulse_abort()

        if p.is_isdn:
            # ISDN: super-fast, clean — second B-channel staggered slightly
            _wait(0.06 * (k - 1))
            _audio.play(isdn_dial_tone(0.12))
            _wait(0.12 + random.uniform(0, 0.15))
            _pulse_abort()
            _audio.play(isdn_progress_tone(1))
            _wait(0.8)
            _pulse_abort()
            _audio.play(isdn_bchan_activate())
            _wait(0.12)
        else:
            # Analog: stagger dials so they don't perfectly overlap (real CO timing)
            _wait(random.uniform(0.0, 0.55) * (k - 1))
            _pulse_abort()
            # Brief dialtone
            _audio.play(dial_tone(0.25))
            _wait(0.25)
            _pulse_abort()
            # DTMF for this link — each modem redials the full number
            for ch in _state.isp_number:
                _pulse_abort()
                buf = silence(0.10) if ch == '-' else dtmf(ch)
                _audio.play(buf)
                _wait(len(buf) / SR)
            _set_link("RINGING")
            _audio.play(ringback(1))
            _wait(5.2 + 0.35 * (k - 1) * int(_state.ml_mode == 1))
            if _state.quit:
                return
            _pulse_abort()
            _set_link("NEGOTIATING")
            # Abbreviated negotiation — per-link tone set detuned (distinct PHY)
            det = 1.0 + (k - 1) * 0.0028
            for freqs in ([1080], [2100, 2400], [1800, 2800]):
                _pulse_abort()
                f_use = [f * det for f in freqs]
                _audio.play(handshake_burst(
                    f_use, 0.22 * p.timing_mult,
                    p.phases[0][2] if p.phases else 0.01,
                    p.phases[0][3] if p.phases else 0.08,
                    p.noise_floor * _scheme_noise_mult))
                _wait(0.25 * p.timing_mult)
                if _state.quit:
                    return
            _pulse_abort()
            _audio.play(carrier_hum(p.carrier_freq * det, 0.25, p.carrier_amp,
                                    p.carrier_jitter * _scheme_jitter_mult))
            _wait(0.25)

        if _state.quit:
            return
        _pulse_abort()
        spd = link_bps
        with _state.lock:
            _state.ml_connected   += 1
            _state.ml_total_speed += spd
            _state.ml_links[lk]["status"] = "ONLINE"
            _state.ml_links[lk]["speed"]  = spd
            _state.isp.status = (f"ONLINE MLPPP  {_state.ml_connected}/{n} links"
                                 f"  {_state.ml_total_speed} bps")
        prefix = "ISDN " if p.is_isdn else ""
        _clog(f"MLPPP link {k}: {prefix}CONNECT {p.max_speed}"
              f"  ({_state.ml_connected}/{n})", "OK")
        _ilog(f"MLPPP link {k} assigned  ({_state.ml_connected}/{n})", "SYS")

    def _link_handshake_thread(k: int):
        try:
            _link_handshake(k)
        except DialAbort:
            ml_thread_abort.set()

    if _state.ml_mode == 0:
        # ── Simultaneous: ALL modems start at once (including first) ─────────
        # The first modem's handshake was already done by _do_single_attempt,
        # so just mark it connected; bring up remaining modems in threads.
        with _state.lock:
            _state.ml_links[0]["status"] = "ONLINE"
            _state.ml_links[0]["speed"]  = link_bps
            _state.ml_connected          = 1
            _state.ml_total_speed        = link_bps
        _clog(f"MLPPP link 1: CONNECT {p.max_speed}  (1/{n})", "OK")
        threads = []
        for k in range(2, n + 1):
            t = threading.Thread(target=_link_handshake_thread, args=(k,), daemon=True)
            threads.append(t)
            t.start()
        for t in threads:
            t.join(timeout=90)
        if ml_thread_abort.is_set() or _state.dial_abort:
            _handle_dial_abort()
            return
    else:
        # ── Serial: one at a time (mark link 1 first, then proceed) ──────────
        with _state.lock:
            _state.ml_links[0]["status"] = "ONLINE"
            _state.ml_links[0]["speed"]  = link_bps
            _state.ml_connected          = 1
            _state.ml_total_speed        = link_bps
        _clog(f"MLPPP link 1: CONNECT {p.max_speed}  (1/{n})", "OK")
        for k in range(2, n + 1):
            if _state.quit:
                break
            try:
                _link_handshake(k)
            except DialAbort:
                _handle_dial_abort()
                return

    if _state.quit:
        return
    _mlppp_bundle_negotiation(n)
    _online_loop()



_FAKE_URLS = [
    "http://www.geocities.com/user123/index.html",
    "http://www.altavista.com/search?q=python+programming",
    "http://www.yahoo.com/news/",
    "http://members.aol.com/coolpage/",
    "http://www.hotmail.com/inbox",
    "http://www.angelfire.com/rock/myband/",
    "http://www.excite.com/weather/",
    "http://www.tripod.com/~user/site.html",
    "http://www.winamp.com/download/winamp295.exe",
    "http://www.irchelp.org/irchelp/mirc/",
]


def _natural_hangup():
    """
    Realistic analog (or ISDN) disconnect sequence.

    Analog: carrier fades -> line crackle -> relay click -> ATH0 -> NO CARRIER
    ISDN  : two descending beeps -> Q.931 RELEASE -> B-channel drop
    """
    p = _state.profile
    if p.is_isdn:
        _sync(isdn_hangup_beep(),
              "--> AT+FCLASS RELEASE  (Q.931 RELEASE sent)", "AT",
              "Q.931 RELEASE received  --  B-channels closing", "SYS")
        _sync(isdn_hangup_beep(),
              "<-- RELEASE COMPLETE  --  ISDN call terminated", "RING",
              "Session closed.  B-channels idle.", "SYS")
    else:
        # Carrier fade-out (amplitude ramp down over 300 ms)
        n   = int(SR * 0.30)
        ph  = 0.0; fade_buf = []
        for i in range(n):
            amp_f = int(AMP * p.carrier_amp * (1.0 - i / n) * 0.9)
            ph   += 2 * math.pi * p.carrier_freq / SR
            fade_buf.append(int(amp_f * math.sin(ph)))
        _sync(fade_buf,
              "--> ATH0  --  initiating hangup", "AT",
              "Remote: carrier loss detected", "SYS")
        _sync(line_noise_burst(0.07, 0.40))
        _sync(speaker_click(0.35),
              "<-- NO CARRIER", "RING",
              "Session closed.", "SYS")


def _page_load_worker(url: str):
    """Background thread: simulates loading a URL over the dial-up connection."""
    p         = _state.profile
    with _state.lock:
        agg = _state.ml_total_speed
        cap = _state.throttle_bps
        lat_extra = _state.extra_latency_ms
        rip = _state.isp_ripoff_mult
        fbk = _state.cust_fightback
    pipe_eff = max(0.22, min(1.0, float(rip) + float(fbk)))
    speed_bps = agg if agg > 0 else _profile_speed_bps(p)
    if cap:
        speed_bps = min(speed_bps, cap)
    speed_bps = max(1200, int(speed_bps))
    kb_s      = speed_bps * pipe_eff / 8 / 1024   # kB/s after "fine print" factor
    total_kb  = random.randint(18, 180)
    hostname  = url.split('/')[2] if '/' in url[8:] else url

    def _set(stage, prog, rx_bytes=0, total_bytes=0):
        with _state.lock:
            _state.page_load_stage    = stage
            _state.page_load_progress = prog
            _state.page_load_bytes    = rx_bytes
            _state.page_load_total    = total_bytes

    # DNS lookup
    _set(f"DNS  resolving  {hostname}", 0.0)
    _clog(f"[HTTP] GET {url}", "SYS")
    _ilog(f"[HTTP] inbound request from {_state.ip_c}", "SYS")
    dns_ms = random.randint(120, 480) + lat_extra
    _wait(dns_ms / 1000)
    if _state.quit or not _state.page_load_active: return
    fake_ip = f"216.{random.randint(1,250)}.{random.randint(1,250)}.{random.randint(1,250)}"
    _set(f"DNS  {hostname}  ->  {fake_ip}", 0.04)
    _clog(f"DNS: {hostname}  A  {fake_ip}  ({dns_ms}ms)", "SYS")

    # TCP connect
    _wait(0.12)
    if _state.quit or not _state.page_load_active: return
    _set(f"TCP  connecting  {fake_ip}:80", 0.08)
    tcp_ms = random.randint(40, 180) + lat_extra // 2
    _wait(tcp_ms / 1000)
    _set(f"TCP  connected   {fake_ip}:80  ({tcp_ms}ms)", 0.12)
    _clog(f"TCP: SYN-ACK from {fake_ip}:80  ({tcp_ms}ms)", "SYS")
    _ilog(f"TCP: connection from {_state.ip_c} to {fake_ip}:80", "SYS")

    # HTTP request
    _wait(0.08)
    if _state.quit or not _state.page_load_active: return
    path = '/' + '/'.join(url.split('/')[3:]) if url.count('/') > 2 else '/'
    _set(f"HTTP GET {path}  ->  200 OK", 0.15)
    req_ms = random.randint(50, 220)
    _wait(req_ms / 1000)
    _clog(f"HTTP/1.0 200 OK  Content-Length: {total_kb}k  ({req_ms}ms)", "SYS")
    _ilog(f"HTTP 200 OK  {total_kb}KB  serving...", "SYS")

    # Transfer
    total_bytes   = total_kb * 1024
    received      = 0
    chunk_kb      = max(1, total_kb // 20)   # ~20 update steps
    chunk_bytes   = chunk_kb * 1024
    chunk_time    = chunk_kb / max(0.1, kb_s * 0.70)   # 70% link util during HTTP
    while received < total_bytes:
        if _state.quit or not _state.page_load_active: return
        _wait(chunk_time)
        with _state.lock:
            ppm = _state.phone_pickup_mode
            pts = _state.phone_pickup_start_ts
        now2 = time.time()
        if ppm == "ALLOW":
            phone_factor = max(0.0, 1.0 - (now2 - pts) / 2.2)
        elif ppm == "RECOVER":
            elapsed2 = now2 - pts
            if elapsed2 < 2.0:
                phone_factor = 1.0 - elapsed2 / 2.0
            elif elapsed2 < 2.5:
                phone_factor = 0.0
            else:
                phone_factor = min(1.0, (elapsed2 - 2.5) / 3.0)
        else:
            phone_factor = 1.0
        recv_inc = int(chunk_bytes * phone_factor)
        received  = min(total_bytes, received + recv_inc)
        prog      = 0.15 + 0.85 * received / total_bytes
        kb_recv   = received // 1024
        pct       = int(100 * received / total_bytes)
        _set(f"RECV  {kb_recv}KB / {total_kb}KB  ({pct}%)", prog, received, total_bytes)
        with _state.lock:
            _state.bytes_rx += recv_inc

    # Done
    _set(f"DONE  {total_kb}KB  in  {int(total_kb/kb_s/0.70)}s", 1.0, total_bytes, total_bytes)
    _clog(f"[HTTP] page loaded  {total_kb}KB", "OK")
    _ilog(f"[HTTP] transfer complete  {total_kb}KB", "OK")
    _wait(1.5)
    with _state.lock:
        _state.page_load_active = False

def sequencer():
    """Master connection lifecycle with automatic redial on failure."""
    _wait(0.6)

    with _state.lock:
        _state.isp.status = "LISTENING  --  awaiting inbound call"
    proto = "ISDN" if getattr(_state.profile, 'is_isdn', False) else "V.90"
    _ilog("Server ready.", "SYS")
    _ilog(f"Pool: {_state.ip_s}/24  protocol: {proto}/PPP/V.42bis", "SYS")
    _ilog(f"Max rate: {_state.profile.max_speed} bps  ({proto})", "SYS")
    _wait(0.4)

    while not _state.quit:
        attempt = _state.attempt
        with _state.lock:
            _state.dial_abort = False
            _state.customer.status = f"DIALLING  (attempt {attempt}/{_state.max_attempts})"
            _state.line_state      = "IDLE"
            _state.progress        = 0.0
            _state.phase_lbl       = ""
            _state.phase_desc      = ""
            _state.final_speed     = ""

        try:
            connected = _do_single_attempt()
        except DialAbort:
            _handle_dial_abort()
            connected = False

        if _state.quit:
            break

        if _state.done:
            break

        if connected:
            _mlppp_connect()        # handles MLPPP then online loop
            if _state.quit or _state.done:
                break
            with _state.lock:
                disk_redial = _state.request_session_redial
                if disk_redial:
                    _state.request_session_redial = False
            if disk_redial:
                _audio.clear()
                with _state.lock:
                    _state.page_load_active = False
                    _state.final_speed = ""
                    _state.line_state = "IDLE"
                    _state.ml_links = []
                    _state.ml_connected = 0
                    _state.ml_total_speed = 0
                    _state.progress = 0.0
                    _state.phase_lbl = ""
                    _state.phase_desc = ""
                    _state.isp.status = "LISTENING  --  awaiting inbound call"
                _ilog("Media swap complete.  Ready for new train.", "SYS")
                # Same attempt number as before — operator fiction "demo disk".
                continue
            break

        # Handle failure / redial
        with _state.lock:
            if _state.attempt >= _state.max_attempts:
                _state.customer.status = "FAILED  --  max retries exceeded"
                _state.line_state      = "FAILED"
                _state.done = True
        # Check done OUTSIDE the lock to avoid deadlock from _clog
        if _state.done:
            _clog("MAX RETRIES EXCEEDED.  Press Q to exit.", "FAIL")
            return
        with _state.lock:
            _state.attempt += 1

        attempt_n = _state.attempt
        _clog(f"Redialling in 3 s  (attempt {attempt_n}/{_state.max_attempts})...", "SYS")
        _ilog("Reset.  Awaiting next call.", "SYS")
        with _state.lock:
            _state.customer.status = f"WAITING  --  redial in 3s"
            _state.isp.status      = "RESET  --  listening"
            _state.line_state      = "REDIAL"
        _wait(3.0)

    # ── Hang up (natural sequence) ──────────────────────────────────────────
    with _state.lock:
        _state.page_load_active = False   # abort any in-progress page load
    # Skip _natural_hangup when a forced-disconnect already played its own audio
    if not getattr(_state, 'forced_disconnect_done', False):
        _natural_hangup()
    if not getattr(_state, 'forced_disconnect_done', False):
        # Normal hang-up: update statuses and show HANGUP state
        with _state.lock:
            _state.customer.status = "DISCONNECTED"
            _state.isp.status      = "IDLE  --  awaiting next call"
            _state.line_state      = "HANGUP"
        _wave('C', 'IDLE'); _wave('I', 'IDLE')
        _stats(0, 0, 0, 0)
        _gap(1.0)
    else:
        # Forced disconnect already set FAILED state and played audio; just pause
        _gap(0.5)
    with _state.lock:
        _state.done = True


# ─────────────────────────────────────────────────────────────────────────────
# WAVEFORM RENDERER
# ─────────────────────────────────────────────────────────────────────────────

def wave_row(width: int, wave: str, frame: int, row: int, rows: int) -> str:
    ch = [' '] * width
    mid = rows // 2

    if wave == 'NOISE':
        chars = r'@#!~*^·:|░▒▓'
        return ''.join(random.choice(chars) for _ in range(width))

    elif wave == 'STATIC':
        # Zoom-specific static: denser and more persistent
        density = 0.25
        return ''.join(random.choice('·.·░ ') if random.random()<density
                       else ' ' for _ in range(width))

    elif wave == 'DTMF':
        for x in range(width):
            y1 = mid + int(rows*0.38 * math.sin(2*math.pi*3.1*x/width + frame*0.50))
            y2 = mid + int(rows*0.22 * math.sin(2*math.pi*7.3*x/width - frame*0.70))
            y3 = mid + int(rows*0.12 * math.sin(2*math.pi*11.5*x/width + frame*0.30))
            if row == int(y1): ch[x] = '|'
            if row == int(y2): ch[x] = ':'
            if row == int(y3): ch[x] = '.'
        return ''.join(ch)

    elif wave == 'SWEEP':
        fv = 0.5 + (frame % 90 / 90.0) * 3.2
        av = rows * 0.44
        for x in range(width):
            y = mid + int(av * math.sin(2*math.pi*fv*x/width + frame*0.18))
            if   row == int(y):        ch[x] = '*'
            elif abs(row-int(y)) == 1: ch[x] = '·'
            elif abs(row-int(y)) == 2: ch[x] = '.'
        return ''.join(ch)

    elif wave == 'CARRIER':
        av = rows * 0.38
        for x in range(width):
            y = mid + int(av * math.sin(2*math.pi*0.80*x/width + frame*0.08))
            if   row == int(y):        ch[x] = '─'
            elif abs(row-int(y)) == 1: ch[x] = '·'
        return ''.join(ch)

    else:   # IDLE
        if row == mid: return '─' * width
        return ' ' * width


# ─────────────────────────────────────────────────────────────────────────────
# CURSES RENDERING
# ─────────────────────────────────────────────────────────────────────────────

_CG = 1; _CC = 2; _CY = 3; _CR = 4; _CM = 5; _CW = 6; _CB = 7; _CO = 8

def _init_colours():
    curses.start_color(); curses.use_default_colors()
    curses.init_pair(_CG, curses.COLOR_GREEN,   -1)
    curses.init_pair(_CC, curses.COLOR_CYAN,    -1)
    curses.init_pair(_CY, curses.COLOR_YELLOW,  -1)
    curses.init_pair(_CR, curses.COLOR_RED,     -1)
    curses.init_pair(_CM, curses.COLOR_MAGENTA, -1)
    curses.init_pair(_CW, curses.COLOR_WHITE,   -1)
    curses.init_pair(_CB, curses.COLOR_BLUE,    -1)
    try: curses.init_pair(_CO, 208, -1)   # orange if terminal supports 256
    except Exception: curses.init_pair(_CO, curses.COLOR_YELLOW, -1)

_TAG = {"AT":_CC,"OK":_CG,"RING":_CY,"NEG":_CM,"SYS":_CW,"FAIL":_CR,"":_CW}
_WAVE_COL = {"NOISE":_CR,"DTMF":_CC,"SWEEP":_CY,"CARRIER":_CG,
             "STATIC":_CR,"IDLE":_CW}

def _sa(w, y, x, s, a=0):
    try: w.addstr(y, x, s, a)
    except curses.error: pass

def _box(w, y, x, h, width, pair, title=""):
    a = curses.color_pair(pair)
    try:
        w.attron(a)
        w.addch(y,   x,       curses.ACS_ULCORNER)
        w.addch(y,   x+width-1, curses.ACS_URCORNER)
        try:
            w.addch(y+h-1, x,       curses.ACS_LLCORNER)
            w.addch(y+h-1, x+width-1, curses.ACS_LRCORNER)
        except curses.error: pass
        for i in range(1, width-1):
            w.addch(y, x+i, curses.ACS_HLINE)
            try: w.addch(y+h-1, x+i, curses.ACS_HLINE)
            except curses.error: pass
        for i in range(1, h-1):
            w.addch(y+i, x,       curses.ACS_VLINE)
            try: w.addch(y+i, x+width-1, curses.ACS_VLINE)
            except curses.error: pass
        w.attroff(a)
    except curses.error: pass
    if title:
        _sa(w, y, x+2, f" {title} ", curses.color_pair(pair)|curses.A_BOLD)

def _bar(w, y, x, lbl, val, maxv, bw, pair):
    fw   = max(2, bw - len(lbl) - 6)
    fill = int((val/maxv)*fw) if maxv else 0
    bar  = '[' + '#'*fill + '-'*(fw-fill) + ']'
    _sa(w, y, x, f"{lbl}{bar}{val:>3}", curses.color_pair(pair))

def _vol_bar_str(vol: float, width: int = 12) -> str:
    """Render a smooth unicode volume bar."""
    filled = int(vol * width / _vol_max)
    empty  = width - filled
    blocks = '█' * filled + '░' * empty
    return f"[{blocks}]"

WAVE_ROWS = 7

def render_modem(win, h, wid, snap: dict, pair: int, frame: int, scroll_offset: int = 0):
    """Render into a dedicated sub-window; coordinates are local (0-based)."""
    win.erase()
    scroll_tag = f"  [SCROLL -{scroll_offset}]" if scroll_offset > 0 else ""
    box_title  = (snap['name'] + scroll_tag)[:wid-4]
    _box(win, 0, 0, h, wid, pair, box_title)
    _sa(win, 1, 2,
        snap['status'][:wid-5].ljust(wid-5),
        curses.color_pair(pair)|curses.A_BOLD)
    log_h    = max(1, h - WAVE_ROWS - 4)
    all_logs = snap['log']
    # scroll_offset 0 = bottom (live); positive = scrolled up into history
    max_off  = max(0, len(all_logs) - log_h)
    scroll_offset = min(scroll_offset, max_off)
    start    = max(0, len(all_logs) - log_h - scroll_offset)
    entries  = all_logs[start : start + log_h]
    for i, (text, tag) in enumerate(entries):
        col = _TAG.get(tag, _CW)
        _sa(win, 2+i, 2, (text[:wid-5]).ljust(wid-5), curses.color_pair(col))
    # ── Scrollbar ─────────────────────────────────────────────────────
    sb_col  = wid - 2          # 1 char inside right border
    total_l = len(all_logs)
    if total_l > log_h and sb_col >= 1:
        track_h  = log_h
        thumb_h  = max(1, int(track_h * log_h / total_l))
        max_off2 = max(1, total_l - log_h)
        # offset 0 = live tail; thumb at bottom; offset max = thumb at top
        thumb_top = int((scroll_offset / max_off2) * (track_h - thumb_h))
        thumb_top = (track_h - thumb_h) - thumb_top  # invert: 0=bottom
        for r in range(track_h):
            ch = chr(0x2588) if thumb_top <= r < thumb_top + thumb_h else chr(0x2591)
            _sa(win, 2 + r, sb_col, ch, curses.color_pair(_CW))
    wave   = snap['wave']
    wcol   = _WAVE_COL.get(wave, _CW)
    wave_y = h - WAVE_ROWS - 1
    wave_w = max(1, wid - 4)
    _sa(win, wave_y-1, 2, '─' * wave_w, curses.color_pair(_CW))
    for row in range(WAVE_ROWS):
        ln = wave_row(wave_w, wave, frame, row, WAVE_ROWS)
        _sa(win, wave_y+row, 2, ln[:wave_w], curses.color_pair(wcol))

def render_line(win, h, wid, snap: dict, frame: int):
    """Render the phone-line strip into its own sub-window."""
    win.erase()
    ls   = snap['line_state']
    prog = snap['progress']
    plbl = snap['phase_lbl']
    pdsc = snap['phase_desc']
    aok  = _audio.ok
    vol  = _vol
    vf   = snap.get('vol_flash', 0)

    lc = {"ONLINE":_CG,"FAILED":_CR,"NEGOTIATING":_CM,
          "DIALLING":_CC,"RINGING":_CY,"REDIAL":_CY,
          "HANGUP":_CR}.get(ls, _CY)

    _box(win, 0, 0, h, wid, lc, f"PHONE LINE  [{ls}]")

    ww  = max(1, wid - 4)
    col = _CW
    if ls == "ONLINE":
        wire = list('─' * ww)
        for _ in range(5):
            wire[(frame * 5 + random.randint(0, ww-1)) % ww] = '▶'
        col = _CG | curses.A_BOLD
        wire_s = ''.join(wire)
    elif ls == "NEGOTIATING":
        wire_s = ''.join(random.choice('~^*·≈░') for _ in range(ww)); col = _CR
    elif ls == "DIALLING":
        wire_s = ''.join(random.choice('DTMF·─') if random.random()<0.25
                         else '─' for _ in range(ww));                 col = _CC
    elif ls == "RINGING":
        wire_s = ('RING──' * (ww//6+2))[:ww];                          col = _CY
    elif ls in ("FAILED", "HANGUP"):
        wire_s = '╌' * ww;                                             col = _CR
    elif ls == "REDIAL":
        wire_s = ('REDIAL·' * (ww//7+2))[:ww];                         col = _CY
    else:
        wire_s = '─' * ww
    _sa(win, 1, 2, wire_s[:ww], curses.color_pair(col))

    bw     = max(4, wid - 10)
    filled = int(prog * bw)
    bar    = '=' * filled + ('>' if filled < bw else '=') + ' ' * max(0, bw-filled-1)
    pct    = int(prog * 100)
    _sa(win, 2, 2, f"[{bar[:bw]}] {pct:>3}%".ljust(wid-4),
        curses.color_pair(_CC) | curses.A_BOLD)
    _sa(win, 3, 2,
        (f"{plbl}  {pdsc}" if plbl else "Waiting...").ljust(wid-4)[:wid-4],
        curses.color_pair(_CM))

    sw = max(8, (wid-6)//2)
    _bar(win, 4, 2,      "SIG ", snap['signal'], 100, sw, _CG)
    _bar(win, 5, 2,      "RX  ", snap['rx'],     100, sw, _CC)
    _bar(win, 4, 2+sw+2, "TX  ", snap['tx'],     100, sw, _CY)
    _bar(win, 5, 2+sw+2, "SNR ", snap['snr'],    60,  sw, _CM)

    def fmt_b(n):
        if n < 1000:    return f"{n} B"
        if n < 1000000: return f"{n/1000:.1f} KB"
        return f"{n/1e6:.2f} MB"
    fs = snap['final_speed']
    if fs:
        brx  = snap['bytes_rx']
        btx  = snap['bytes_tx']
        ml_n = snap.get('ml_count', 1)
        ml_ts = int(snap.get('ml_total_speed', 0) or 0)
        cap  = snap.get('throttle_bps')
        fs_bps = int(''.join(c for c in str(fs) if c.isdigit()) or '0')
        # Show live effective rate:
        # - MLPPP: aggregate current bundle rate
        # - single-link: initial CONNECT rate
        # - shaping cap applies to both
        disp_bps = ml_ts if (ml_n > 1 and ml_ts > 0) else fs_bps
        if cap:
            disp_bps = min(disp_bps, int(cap))
        rip = float(snap.get('isp_ripoff_mult', 1.0))
        fbk = float(snap.get('cust_fightback', 0.0))
        peff = max(0.22, min(1.0, rip + fbk))
        disp_eff = int(disp_bps * peff)
        rip_s = ""
        if peff < 0.995:
            rip_s = f"  eff:{disp_eff}"
        cap_s = (f"  SHAPED:{cap}" if cap else "") + rip_s
        info = (f"  {disp_bps} bps  V.90/V.42bis  "
                f"RX:{fmt_b(brx)}  TX:{fmt_b(btx)}  "
                f"PING:{snap['ping_ms']}ms  "
                f"attempt {snap['attempt']}/{snap['max_attempts']}{cap_s}")
        _sa(win, 6, 2, info[:wid-4].ljust(wid-4),
            curses.color_pair(_CG) | curses.A_BOLD)
    else:
        _sa(win, 6, 2, ' ' * (wid-4))

    # ── MLPPP per-link table + page-load bar ──────────────────────────────
    ml_n     = snap.get('ml_count', 1)
    ml_cn    = snap.get('ml_connected', 0)
    ml_ts    = snap.get('ml_total_speed', 0)
    ml_m     = snap.get('ml_mode', 0)
    ml_links = snap.get('ml_links', [])
    row_off  = 0
    if ml_n > 1:
        mode_s = 'SIM' if ml_m == 0 else 'SER'
        hdr = f"MLPPP [{mode_s}]  {ml_cn}/{ml_n}  {ml_ts} bps"
        _sa(win, 7, 2, hdr[:wid-4].ljust(wid-4),
            curses.color_pair(_CC) | curses.A_BOLD)
        row_off = 1
        # Show up to 4 link status tiles side-by-side
        tile_w  = max(8, (wid - 4) // min(4, ml_n))
        for li, lnk in enumerate(ml_links[:4]):
            st = lnk.get('status', '?')
            lc_map = {'ONLINE': _CG, 'NEGOTIATING': _CM, 'RINGING': _CY,
                      'DIALLING': _CC, 'IDLE': _CW}
            lc = lc_map.get(st, _CW)
            tile = f"L{lnk['n']}:{st[:6]}"
            _sa(win, 8, 2 + li * tile_w, tile[:tile_w].ljust(tile_w),
                curses.color_pair(lc))
        row_off = 2
    # Page-load bar
    if snap.get('page_load_active'):
        stage = snap.get('page_load_stage', '')
        prog  = snap.get('page_load_progress', 0.0)
        bw    = max(4, wid - 4 - len(stage) - 6)
        fill  = int(prog * bw)
        bar   = '=' * fill + '>' + ' ' * max(0, bw - fill - 1)
        pct   = int(prog * 100)
        _sa(win, 7 + row_off, 2,
            f"{stage}  [{bar[:bw]}]{pct:>3}%"[:wid-4].ljust(wid-4),
            curses.color_pair(_CG))
        row_off += 1

    # HTTP activity feed -- visible while connected (rows 7+row_off .. 8+row_off)
    ol = snap.get('online_lines', [])
    if snap['line_state'] == "ONLINE" and ol:
        for i, ln in enumerate(ol[-2:]):
            _sa(win, 7+row_off+i, 2, f" > {ln}"[:wid-4].ljust(wid-4),
                curses.color_pair(_CG))
    else:
        # Clear rows when not online so stale lines don't linger
        _sa(win, 7+row_off, 2, ' ' * max(0, wid-4))
        _sa(win, 8+row_off, 2, ' ' * max(0, wid-4))

    # Debug row (shown when debug mode is active)
    if snap.get('debug'):
        fp    = snap.get('fail_prob', 0)
        flab  = "ALWAYS" if fp > 1.0 else f"{fp*100:.0f}%"
        num   = snap.get('isp_number', '')
        freqs = snap.get('dbg_freqs', '')
        fm    = snap.get('dbg_fm', 0.0)
        nm    = snap.get('dbg_nm', 0.0)
        dur   = snap.get('dbg_phase_dur', 0.0)
        dbg   = (f"[DBG] num:{num}  fail:{flab}  "
                 f"freqs:{freqs}  fm:{fm:.2f}  nm:{nm:.2f}  "
                 f"phase_dur:{dur:.3f}s")
        _sa(win, h-3, 2, dbg[:wid-4].ljust(wid-4),
            curses.color_pair(_CY))

    # Volume bar -- flashes brighter when just changed
    vol_bar = _vol_bar_str(vol, 12)
    pct_vol = int(vol / _vol_max * 100)
    vol_col = (_CY | curses.A_BOLD) if vf > 0 else _CG
    audio_s = f"AUDIO:{'OK' if aok else 'SILENT'}  VOL{vol_bar}{pct_vol:>3}%"
    dbg_ind = "  [DBG]" if snap.get('debug') else ""
    hint    = f"[Q] QUIT  [+/-/]/[] VOL  [D]DBG  [W]LOAD  [C/I]CTRL{dbg_ind}"
    _sa(win, h-2, 2, audio_s[:wid//2].ljust(wid//2), curses.color_pair(vol_col))
    _sa(win, h-2, wid-len(hint)-3, hint,              curses.color_pair(_CW))


def render_online_sidebar(win, y, x, h, wid, snap: dict):
    """Small activity feed shown when online."""
    _box(win, y, x, h, wid, _CG, "DATA ACTIVITY")
    lines = snap['online_lines'][-(h-2):]
    for i, ln in enumerate(lines):
        _sa(win, y+1+i, x+2, ln[:wid-4], curses.color_pair(_CG))


def _snapshot() -> dict:
    with _state.lock:
        return {
            'line_state':  _state.line_state,
            'progress':    _state.progress,
            'phase_lbl':   _state.phase_lbl,
            'phase_desc':  _state.phase_desc,
            'signal':      _state.signal,
            'rx':          _state.rx,
            'tx':          _state.tx,
            'snr':         _state.snr,
            'final_speed': _state.final_speed,
            'ip_c':        _state.ip_c,
            'ip_s':        _state.ip_s,
            'done':        _state.done,
            'quit':        _state.quit,
            'attempt':     _state.attempt,
            'max_attempts':_state.max_attempts,
            'bytes_rx':    _state.bytes_rx,
            'bytes_tx':    _state.bytes_tx,
            'ping_ms':     _state.ping_ms,
            'online_lines':list(_state.online_lines),
            'vol_flash':   _state.vol_flash,
            'isp_number':  _state.isp_number,
            'isp_label':   _state.isp_label,
            'fail_prob':   _state.fail_prob,
            'debug':       _state.debug,
            'dbg_phase_dur': _state.dbg_phase_dur,
            'dbg_freqs':   _state.dbg_freqs,
            'dbg_fm':      _state.dbg_fm,
            'dbg_nm':      _state.dbg_nm,
            'customer': {'name':_state.customer.name,
                         'status':_state.customer.status,
                         'wave':_state.customer.wave,
                         'log':list(_state.customer.log)},
            'isp':      {'name':_state.isp.name,
                         'status':_state.isp.status,
                         'wave':_state.isp.wave,
                         'log':list(_state.isp.log)},
            'ml_count':       _state.ml_count,
            'ml_mode':        _state.ml_mode,
            'ml_connected':   _state.ml_connected,
            'ml_total_speed': _state.ml_total_speed,
            'ml_links':       list(_state.ml_links),
            'page_load_active':   _state.page_load_active,
            'page_load_url':      _state.page_load_url,
            'page_load_stage':    _state.page_load_stage,
            'page_load_progress': _state.page_load_progress,
            'page_load_bytes':    _state.page_load_bytes,
            'page_load_total':    _state.page_load_total,
            'overlay':            _state.overlay,
            'overlay_sel':        _state.overlay_sel,
            'modal_title':        _state.modal_title,
            'modal_message':      _state.modal_message,
            'modal_kind':         _state.modal_kind,
            'modal_options':     list(_state.modal_options),
            'modal_sel':          _state.modal_sel,
            'modal_context':      _state.modal_context,
            'throttle_bps':       _state.throttle_bps,
            'isp_ripoff_mult':    _state.isp_ripoff_mult,
            'cust_fightback':     _state.cust_fightback,
        }


# ─────────────────────────────────────────────────────────────────────────────
# STARTUP MENU
# ─────────────────────────────────────────────────────────────────────────────

_BANNER = [
    " ██████╗ ██╗ █████╗ ██╗     ██╗   ██╗██████╗",
    " ██╔══██╗██║██╔══██╗██║     ██║   ██║██╔══██╗",
    " ██║  ██║██║███████║██║     ██║   ██║██████╔╝",
    " ██║  ██║██║██╔══██║██║     ██║   ██║██╔═══╝",
    " ██████╔╝██║██║  ██║███████╗╚██████╔╝██║    ",
    " ╚═════╝ ╚═╝╚═╝  ╚═╝╚══════╝ ╚═════╝ ╚═╝    ",
    "   L O C A L   M O D E M   S I M U L A T O R   ",
]

_MODEM_CHARS = {
    "USRobotics Sportster 56K V.90": "Rich resonant bong · deep negotiation · mid-range carrier",
    "Hayes Optima 56K V.90": "Precise clean tones · clinical V.34 · quiet steady carrier",
    "Zoom 56K V.90  (budget)": "Grinding noise · heavy static · wobbly carrier · pops",
    "Motorola ModemSURFR 56K": "High-frequency bright tones · rapid DSP · clean fast chirp",
}

def startup_menu(stdscr) -> tuple:
    """
    Scrollable startup menu.
    Tab/Shift-Tab  : cycle focus between sections.
    Arrow keys     : navigate within focused section.
    Space          : open/close accordion (advanced sections).
    Enter          : confirm all settings and connect.
    +/-  or  ]/[   : adjust volume.
    D              : toggle debug mode.
    Q / Esc        : quit.
    """
    global _vol, _scheme_idx, _scheme_noise_mult, _scheme_jitter_mult, _scheme_force_silent
    _init_colours()
    curses.curs_set(0)
    stdscr.timeout(80)

    sel_mod      = 0
    sel_fail     = 0
    sel_num      = 0
    _CUSTOM_NUM_IDX = len(ISP_NUMBERS) - 1   # last entry is the editable custom slot
    custom_num   = ISP_NUMBERS[_CUSTOM_NUM_IDX][0]   # starts with the default placeholder
    sel_attempts = 4
    debug        = False

    adv_err_open   = False
    adv_err_sel    = 0
    sc_weights     = [1.0] * len(_FAIL_SCENARIOS)

    adv_snd_open   = False
    sel_snd        = 0

    adv_ml_open    = False
    ml_count       = 1
    ml_mode        = 0
    adv_ml_sub     = 0

    # focus: 0=modem 2=ISP 1=fail 3=attempts 4=err_acc 5=snd_acc 6=ml_acc
    _FC    = (0, 2, 1, 3, 4, 5, 6)
    focus  = 0
    frame  = 0
    menu_scroll = 0     # rows scrolled down (0 = top)

    def _saferow(stdscr, row, col, text, attr=0):
        """Draw only if row is within the visible content area."""
        my2, mx2 = stdscr.getmaxyx()
        content_top = len(_BANNER) + 3
        avail       = my2 - content_top - 1
        # rel is the row relative to content start, adjusted for scroll
        vis = row - content_top - menu_scroll
        if 0 <= vis < avail:
            _sa(stdscr, content_top + vis, col, text, attr)

    def _shift(y):
        """Convert absolute content row to visible screen row, or -1 if hidden."""
        content_top = len(_BANNER) + 3
        return content_top + (y - content_top - menu_scroll)

    def _sarow(w, y, x, s, a=0):
        """stdscr-aware addstr that maps content y to screen y via scroll."""
        vy = _shift(y)
        my2, _ = w.getmaxyx()
        if 0 <= vy < my2:
            _sa(w, vy, x, s, a)

    def _boxrow(w, y, x, h, width, pair, title=""):
        """Draw box at content-y, scroll-adjusted."""
        vy = _shift(y)
        my2, _ = w.getmaxyx()
        if vy + h < 0 or vy >= my2: return
        # temporarily paint row by row
        a = curses.color_pair(pair)
        try:
            w.attron(a)
            if 0 <= vy < my2:
                w.addch(vy, x, curses.ACS_ULCORNER)
                w.addch(vy, x+width-1, curses.ACS_URCORNER)
                for i in range(1, width-1): w.addch(vy, x+i, curses.ACS_HLINE)
            vy_bot = vy + h - 1
            if 0 <= vy_bot < my2:
                try:
                    w.addch(vy_bot, x, curses.ACS_LLCORNER)
                    w.addch(vy_bot, x+width-1, curses.ACS_LRCORNER)
                    for i in range(1, width-1): w.addch(vy_bot, x+i, curses.ACS_HLINE)
                except curses.error: pass
            for i in range(1, h-1):
                vr = vy + i
                if 0 <= vr < my2:
                    w.addch(vr, x, curses.ACS_VLINE)
                    try: w.addch(vr, x+width-1, curses.ACS_VLINE)
                    except curses.error: pass
            w.attroff(a)
        except curses.error: pass
        if title:
            vyt = vy
            if 0 <= vyt < my2:
                _sa(w, vyt, x+2, f" {title} ", curses.color_pair(pair)|curses.A_BOLD)

    def _draw_accordion_hdr(y, lbl, open_, focused, pair_open, hint="", extra=""):
        arrow = "[-]" if open_ else "[+]"
        fhint = f"  {hint}" if hint else ""
        line  = f" {arrow} {lbl}{extra}{fhint}"
        col   = curses.color_pair(pair_open) | curses.A_BOLD if focused \
                else curses.color_pair(_CW)
        _sarow(stdscr, y, box_x+1, line[:box_w-2], col)

    while True:
        stdscr.erase()
        my, mx = stdscr.getmaxyx()
        frame += 1
        content_top = len(_BANNER) + 3
        avail_h     = my - content_top - 1   # rows available for scrollable content

        # ── Banner (always visible, not scrolled) ───────────────────────────
        blen = max(len(l) for l in _BANNER)
        bx   = max(0, (mx - blen) // 2)
        for i, ln in enumerate(_BANNER):
            col = _CG if i < 6 else _CC
            _sa(stdscr, 1+i, bx, ln, curses.color_pair(col)|curses.A_BOLD)

        box_w = min(74, mx-4)
        box_x = max(0, (mx-box_w)//2)

        # ── Compute content rows ──────────────────────────────────────────────
        cy = content_top   # running content cursor (absolute)

        # ── Modem list ────────────────────────────────────────────────────────
        lh = len(PROFILES) + 2
        lc = _CG if focus == 0 else _CW
        _boxrow(stdscr, cy, box_x, lh, box_w, lc,
                f"SELECT MODEM  [↑↓ move  Tab=next  {len(PROFILES)} options]")
        for i, p in enumerate(PROFILES):
            cursor = "▶ " if i == sel_mod else "  "
            attr   = curses.color_pair(_CY)|curses.A_BOLD if i == sel_mod \
                     else curses.color_pair(_CW)
            tag    = " [ISDN]" if getattr(p, 'is_isdn', False) else ""
            _sarow(stdscr, cy+1+i, box_x+2,
                   f"{cursor}{p.name:<42}{tag} {p.max_speed:>7} bps"[:box_w-4], attr)
        dp    = PROFILES[sel_mod]
        cy   += lh
        _sarow(stdscr, cy,   box_x+2, dp.description[:box_w-4], curses.color_pair(_CM))
        _sarow(stdscr, cy+1, box_x+2,
               f"Audio: {_MODEM_CHARS.get(dp.name,'')}"[:box_w-4],
               curses.color_pair(_CY))
        cy += 3

        # ── ISP phone number ──────────────────────────────────────────────────
        nlc = _CG if focus == 2 else _CW
        editing_custom = (focus == 2 and sel_num == _CUSTOM_NUM_IDX)
        num_hint = "type number  Bksp=delete  Tab=next" if editing_custom else "↑↓ select  Tab=next"
        _boxrow(stdscr, cy, box_x, len(ISP_NUMBERS)+2, box_w, nlc,
                f"ISP PHONE NUMBER  [{num_hint}]")
        for i, (num, lbl) in enumerate(ISP_NUMBERS):
            is_custom = (i == _CUSTOM_NUM_IDX)
            cursor = "▶ " if i == sel_num else "  "
            attr   = curses.color_pair(_CY)|curses.A_BOLD if i == sel_num \
                     else curses.color_pair(_CW)
            if is_custom:
                display_num = (custom_num + "_") if editing_custom else custom_num
                _, lbl_suffix = lbl.split("--", 1)
                _sarow(stdscr, cy+1+i, box_x+2,
                       f"{cursor}{display_num:<15} custom --{lbl_suffix}"[:box_w-4], attr)
            else:
                _sarow(stdscr, cy+1+i, box_x+2,
                       f"{cursor}{num:<14}  {lbl}"[:box_w-4], attr)
        cy += len(ISP_NUMBERS) + 3

        # ── Failure preset ────────────────────────────────────────────────────
        flc = _CY if focus == 1 else _CW
        _boxrow(stdscr, cy, box_x, 3, box_w, flc,
                "FAILURE RATE  [← → select  Tab=next]")
        fx  = box_x + 3
        gap = (box_w-10) // len(FAIL_OPTIONS)
        for i, (lbl, _prob) in enumerate(FAIL_OPTIONS):
            sel  = (i == sel_fail)
            attr = curses.color_pair(_CR)|curses.A_BOLD if sel else curses.color_pair(_CW)
            tag  = f"[{lbl}]" if sel else f" {lbl} "
            _sarow(stdscr, cy+1, fx + i*gap, tag[:gap], attr)
        cy += 4

        # ── Max attempts ──────────────────────────────────────────────────────
        alc = _CC if focus == 3 else _CW
        _boxrow(stdscr, cy, box_x, 3, box_w, alc,
                "MAX DIAL ATTEMPTS  [← → change  Tab=next]")
        ax_lbl = f"  ◀  {sel_attempts:>2} attempts  ▶   (range 1–20)"
        _sarow(stdscr, cy+1, box_x+2, ax_lbl[:box_w-4],
               curses.color_pair(_CY)|curses.A_BOLD if focus == 3
               else curses.color_pair(_CW))
        cy += 4

        # ── ADV: per-scenario error weights ───────────────────────────────────
        sc_sum = ", ".join(f"{_FAIL_SCENARIOS[i][0].split()[0]}:{sc_weights[i]:.1f}"
                           for i in range(len(_FAIL_SCENARIOS)) if sc_weights[i] != 1.0) or "uniform"
        _draw_accordion_hdr(cy, "ADVANCED: FAILURE TUNING",
                            adv_err_open, focus == 4, _CR,
                            hint="Space=expand  ↑↓ row  ← → weight  Tab=next",
                            extra=f"  ({sc_sum})")
        cy += 1
        if adv_err_open:
            inner_x = box_x + 4
            for si, (slbl, _, _, _) in enumerate(_FAIL_SCENARIOS):
                w2  = sc_weights[si]
                bw2 = 10
                fl2 = int(w2 / 5.0 * bw2)
                wbar = '█' * fl2 + '░' * (bw2 - fl2)
                hl   = (focus == 4 and si == adv_err_sel)
                attr = curses.color_pair(_CR)|curses.A_BOLD if hl else curses.color_pair(_CW)
                cur  = "▶ " if hl else "  "
                _sarow(stdscr, cy+si, inner_x,
                       f"{cur}{slbl:<22} [{wbar}] {w2:.1f}  ← →"[:box_w-6], attr)
            cy += len(_FAIL_SCENARIOS) + 1

        # ── ADV: sound scheme ─────────────────────────────────────────────────
        snd_lbl = _SOUND_SCHEMES[sel_snd][0]
        _draw_accordion_hdr(cy, "ADVANCED: SOUND SCHEME",
                            adv_snd_open, focus == 5, _CM,
                            hint="Space=expand  ↑↓ cycle  Tab=next",
                            extra=f"  [{snd_lbl}]")
        cy += 1
        if adv_snd_open:
            inner_x = box_x + 4
            for si, (name, nmult, jmult, fsilent) in enumerate(_SOUND_SCHEMES):
                hl   = (si == sel_snd)
                attr = curses.color_pair(_CM)|curses.A_BOLD if hl else curses.color_pair(_CW)
                desc = ("force silent" if fsilent else f"noise x{nmult:.1f}  jitter x{jmult:.1f}")
                cur  = "▶ " if hl else "  "
                _sarow(stdscr, cy+si, inner_x,
                       f"{cur}{name:<18}  {desc}"[:box_w-6], attr)
            cy += len(_SOUND_SCHEMES) + 1

        # ── ADV: multi-link PPP ───────────────────────────────────────────────
        ml_lbl = (f"{ml_count} modem{'s' if ml_count > 1 else ''}"
                  + (f"  ({'simultaneous' if ml_mode == 0 else 'serial'})"
                     if ml_count > 1 else ""))
        _draw_accordion_hdr(cy, "ADVANCED: MULTI-LINK PPP",
                            adv_ml_open, focus == 6, _CC,
                            hint="Space=expand  ↑↓ row  ← → change  Tab=next",
                            extra=f"  [{ml_lbl}]")
        cy += 1
        if adv_ml_open:
            inner_x = box_x + 4
            # Row 0: modem count
            hl0  = (focus == 6 and adv_ml_sub == 0)
            a0   = curses.color_pair(_CC)|curses.A_BOLD if hl0 else curses.color_pair(_CW)
            _sarow(stdscr, cy, inner_x,
                   f"{'▶ ' if hl0 else '  '}Modems: ◀  {ml_count:>2}  ▶   (1–20  ← →)"[:box_w-6], a0)
            # Row 1: bonding mode
            hl1  = (focus == 6 and adv_ml_sub == 1)
            a1   = curses.color_pair(_CC)|curses.A_BOLD if hl1 else curses.color_pair(_CW)
            modes = ["Simultaneous  (Win XP -- all bond at once)",
                     "Serial        (Win ME -- one at a time)"]
            _sarow(stdscr, cy+1, inner_x,
                   f"{'▶ ' if hl1 else '  '}Mode:   {modes[ml_mode]}"[:box_w-6], a1)
            # Row 2: aggregate speed
            spd = int(PROFILES[sel_mod].max_speed.replace(',','')) * ml_count \
                  if PROFILES[sel_mod].max_speed.isdigit() \
                  else int(''.join(c for c in PROFILES[sel_mod].max_speed if c.isdigit()) or '0') * ml_count
            _sarow(stdscr, cy+2, inner_x,
                   f"  Aggregate: {spd} bps  ({ml_count} x {PROFILES[sel_mod].max_speed})"[:box_w-6],
                   curses.color_pair(_CY))
            cy += 4

        # total content height
        total_content_h = cy - content_top

        # ── Debug + volume ────────────────────────────────────────────────────
        dbg_col = curses.color_pair(_CR)|curses.A_BOLD if debug else curses.color_pair(_CW)
        dbg_tag = "[ON]" if debug else "[OFF]"
        _sarow(stdscr, cy, box_x+2,
               f"DEBUG {dbg_tag} (D)   VOL {_vol_bar_str(_vol, 10)}"
               f"  {int(_vol/_vol_max*100):>3}%  (+/- or ]/[)", dbg_col)

        # ── Enter prompt ──────────────────────────────────────────────────────
        pulse = abs(math.sin(frame * 0.08))
        ac    = _CG if pulse > 0.5 else _CW
        _sarow(stdscr, cy+2, box_x+2,
               "Press  ENTER  to connect  (Space = expand/collapse accordions)",
               curses.color_pair(ac)|curses.A_BOLD)

        # ── Scroll indicators ─────────────────────────────────────────────────
        if menu_scroll > 0:
            _sa(stdscr, content_top, mx-4, " ▲ ", curses.color_pair(_CY)|curses.A_BOLD)
        if total_content_h - menu_scroll > avail_h:
            _sa(stdscr, my-2, mx-4, " ▼ ", curses.color_pair(_CY)|curses.A_BOLD)
        # Scrollbar track on right edge
        if total_content_h > avail_h and avail_h > 2:
            track_h  = avail_h
            thumb_sz = max(1, int(track_h * avail_h / total_content_h))
            thumb_t  = int(menu_scroll / max(1, total_content_h - avail_h)
                           * (track_h - thumb_sz))
            for r in range(track_h):
                ch = '█' if thumb_t <= r < thumb_t + thumb_sz else '░'
                _sa(stdscr, content_top + r, mx-1, ch, curses.color_pair(_CW))

        stdscr.refresh()

        # ── Input ──────────────────────────────────────────────────────────────
        key = stdscr.getch()

        # Tab cycles focus
        if key in (ord('\t'), curses.KEY_BTAB):
            focus = _FC[(_FC.index(focus) + 1) % len(_FC)]
            # Auto-scroll to keep focused section visible (rough heuristic)
            # Just ensure we scroll down if we exceed avail_h
            menu_scroll = max(0, min(menu_scroll, max(0, total_content_h - avail_h)))

        # Arrow keys
        if key == curses.KEY_UP:
            if   focus == 0: sel_mod = max(0, sel_mod - 1)
            elif focus == 2: sel_num = max(0, sel_num - 1)
            elif focus == 4 and adv_err_open: adv_err_sel = max(0, adv_err_sel - 1)
            elif focus == 5 and adv_snd_open: sel_snd = max(0, sel_snd - 1)
            elif focus == 6 and adv_ml_open:  adv_ml_sub  = max(0, adv_ml_sub - 1)
            else: menu_scroll = max(0, menu_scroll - 1)
        if key == curses.KEY_DOWN:
            if   focus == 0: sel_mod = min(len(PROFILES)-1, sel_mod + 1)
            elif focus == 2: sel_num = min(len(ISP_NUMBERS)-1, sel_num + 1)
            elif focus == 4 and adv_err_open:
                adv_err_sel = min(len(_FAIL_SCENARIOS)-1, adv_err_sel + 1)
            elif focus == 5 and adv_snd_open: sel_snd = min(len(_SOUND_SCHEMES)-1, sel_snd + 1)
            elif focus == 6 and adv_ml_open:
                adv_ml_sub = min(1, adv_ml_sub + 1)
            else: menu_scroll = min(max(0, total_content_h - avail_h),
                                    menu_scroll + 1)
        if key == curses.KEY_LEFT:
            if   focus == 1: sel_fail     = max(0, sel_fail - 1)
            elif focus == 3: sel_attempts = max(1, sel_attempts - 1)
            elif focus == 4 and adv_err_open:
                sc_weights[adv_err_sel] = round(max(0.0, sc_weights[adv_err_sel] - 0.5), 1)
            elif focus == 6 and adv_ml_open:
                if adv_ml_sub == 0: ml_count = max(1, ml_count - 1)
                else:               ml_mode  = max(0, ml_mode  - 1)
        if key == curses.KEY_RIGHT:
            if   focus == 1: sel_fail     = min(len(FAIL_OPTIONS)-1, sel_fail + 1)
            elif focus == 3: sel_attempts = min(20, sel_attempts + 1)
            elif focus == 4 and adv_err_open:
                sc_weights[adv_err_sel] = round(min(5.0, sc_weights[adv_err_sel] + 0.5), 1)
            elif focus == 6 and adv_ml_open:
                if adv_ml_sub == 0: ml_count = min(20, ml_count + 1)
                else:               ml_mode  = min(1,  ml_mode  + 1)
        # Custom number text entry: when focused on ISP number and custom slot selected,
        # printable characters are appended and backspace removes the last character.
        if focus == 2 and sel_num == _CUSTOM_NUM_IDX:
            if key in (curses.KEY_BACKSPACE, 127, 8):
                custom_num = custom_num[:-1]
            elif 0 <= key <= 0x10ffff and chr(key) in '0123456789-()+': # allowlist: digits and valid phone punctuation only
                if len(custom_num) < 20:
                    custom_num += chr(key)

        # Page Up/Down scrolls the menu
        if key == curses.KEY_PPAGE:
            menu_scroll = max(0, menu_scroll - (avail_h // 2))
        if key == curses.KEY_NPAGE:
            menu_scroll = min(max(0, total_content_h - avail_h),
                              menu_scroll + (avail_h // 2))

        # Space: toggle accordion (never connects)
        if key == ord(' '):
            if   focus == 4: adv_err_open = not adv_err_open
            elif focus == 5: adv_snd_open = not adv_snd_open
            elif focus == 6: adv_ml_open  = not adv_ml_open

        # Enter: ALWAYS connect (never toggles accordion)
        if key in (10, 13, curses.KEY_ENTER):
            break

        # Misc
        if key in (ord('d'), ord('D')): debug = not debug
        if key in (ord('+'), ord('='), ord(']')):
            _vol = min(_vol_max, round(_vol + _vol_step, 1))
        if key in (ord('-'), ord('['))  :
            _vol = max(_vol_min, round(_vol - _vol_step, 1))
        if key == curses.KEY_MOUSE:
            try: curses.getmouse()
            except curses.error: pass
        if key in (ord('q'), ord('Q')):
            return None, None, None, None, False, None, 0, 1, 0, ""

    _scheme_idx                             = sel_snd
    _, _scheme_noise_mult, _scheme_jitter_mult, _scheme_force_silent = _SOUND_SCHEMES[sel_snd]

    return (sel_mod, sel_fail, sel_num, sel_attempts, debug,
            sc_weights, sel_snd, ml_count, ml_mode, custom_num)



# ── Overlay actions ──────────────────────────────────────────────────────────
_OVERLAY_CUST_ACTIONS = [
    ("Inject line noise (toggle)",       "inject_noise"),
    ("Toggle modem speaker",            "toggle_speaker"),
    ("Force disconnect (ATH)",          "force_disconnect"),
    ("Reset AT register (ATZ)",         "reset_at"),
    ("Simulate call-waiting beep",     "callwait"),
    ("Request line retrain (+MS)",     "line_retrain"),
    ("Boost: 'compressor voodoo'",      "cust_placebo_boost"),
    ("Fight back: FTC complaint fax", "cust_ftc_complaint"),
    ("Fight back: modem lawyer",      "cust_modem_lawyer"),
    ("Swap demo floppy disk + redial", "cust_demo_floppy_redial"),
    ("Someone else answers the phone (joke)", "cust_phone_pickup_joke"),
]
_OVERLAY_ISP_ACTIONS = [
    ("Force client disconnect",           "isp_disconnect"),
    ("Degrade line (+noise / jitter)",    "isp_degrade"),
    ("Reset NAS port",                   "isp_reset_port"),
    ("Inject upstream noise (toggle)",    "isp_noise"),
    ("Cap speed at 28.8k (shaping)",     "isp_throttle"),
    ("Remove bandwidth cap",             "isp_clear_throttle"),
    ("Add shaper delay (+RTT)",          "isp_latency"),
    ("Ripoff: shrink pipe (fine print)", "isp_ripoff_shrink"),
    ("Ripoff: DNS 'helper' redirects",   "isp_dns_hijack"),
    ("Ripoff: inject interstitial ads",  "isp_ad_inject"),
    ("Ripoff: surge billing notices",    "isp_surge_toggle"),
    ("Ripoff: spam fake ToS amendments", "isp_fake_tos_spam"),
]


def _show_modal(title: str, message: str) -> None:
    """Show an info modal. Dismiss with Enter."""
    with _state.lock:
        _state.modal_title = title
        _state.modal_message = message
        _state.modal_kind = "info"
        _state.modal_options = []
        _state.modal_sel = 0


def _show_modal_choice(title: str, message: str, options: List[Tuple[str, str]],
                       context: str = "phone_pickup") -> None:
    """
    Show a choice modal.

    options: list[(option_id, label_to_display)].
    context: handler tag used by the dispatch loop to route the confirmed choice.
    Dismiss/apply with Enter; cancel with Esc.
    """
    with _state.lock:
        _state.modal_title   = title
        _state.modal_message = message
        _state.modal_kind    = "choice"
        _state.modal_options = list(options)
        _state.modal_sel     = 0
        _state.modal_context = context


def _clear_modal() -> None:
    with _state.lock:
        _state.modal_title   = None
        _state.modal_message = None
        _state.modal_kind    = None
        _state.modal_options = []
        _state.modal_sel     = 0
        _state.modal_context = None


def _apply_phone_pickup_choice(choice_id: str) -> None:
    """
    Phone-pickup joke:
      - allow_pickup: line degrades to zero and stays there.
      - stop_pickup: line degrades, then returns.
    """
    if choice_id == "allow_pickup":
        mode = "ALLOW"
        _audio.play_now(pop_static(0.22))
        _audio.play(call_waiting_tone())
        with _state.lock:
            _state.phone_pickup_mode = mode
            _state.phone_pickup_start_ts = time.time()
        _clog("Operator chose: allow someone else to answer", "SYS")
        _ilog("Subscriber line: off-hook interference detected", "FAIL")
    else:
        mode = "RECOVER"
        _audio.play_now(line_noise_burst(0.10, 0.30))
        _audio.play(call_waiting_tone())
        with _state.lock:
            _state.phone_pickup_mode = mode
            _state.phone_pickup_start_ts = time.time()
        _clog("Operator chose: tell them to stop answering", "OK")
        _ilog("Subscriber line: warning sent, interference abates", "SYS")


def _apply_isp_shrink_choice(factor_str: str) -> None:
    """
    ISP ripoff shrink-pipe: apply the chosen speed factor.
    factor_str is the string representation of the target multiplier,
    e.g. '0.75'.  The result is clamped to [0.1, current] so the ISP
    can only shrink (never accidentally restore) and never below 0.1.
    """
    try:
        factor = float(factor_str)
    except ValueError:
        return
    factor = max(0.1, factor)
    with _state.lock:
        new_mult = max(0.1, round(_state.isp_ripoff_mult * factor, 4))
        _state.isp_ripoff_mult = new_mult
        m = new_mult
    _ilog(f"[REV] hidden throughput factor now ~{m:.2f}  (subscriber pays full)", "SYS")
    _clog("[FINE PRINT] Performance may not match advertised  --  you agreed", "FAIL")


def _apply_overlay_action(tag: str) -> None:
    """Execute overlay menu action; safe while dialling except where modal says otherwise."""
    global _scheme_noise_mult, _scheme_jitter_mult
    with _state.lock:
        ls = _state.line_state

    def _need_online() -> bool:
        if ls != "ONLINE":
            _show_modal(
                "Not connected",
                "That control needs an active link. Finish negotiating or try again after CONNECT.",
            )
            return True
        return False

    if tag == "inject_noise":
        with _state.lock:
            _state.inject_noise = not _state.inject_noise
            on = _state.inject_noise
        _clog(f"Line noise injection  {'ON' if on else 'OFF'}  (operator panel)", "SYS")
        return

    if tag == "toggle_speaker":
        with _state.lock:
            _state.speaker_enabled = not _state.speaker_enabled
            on = _state.speaker_enabled
        _audio.play(speaker_click(0.28))
        _clog(f"Speaker relay  {'ON' if on else 'OFF'}", "AT")
        return

    if tag == "callwait":
        _audio.play(call_waiting_tone())
        _clog("[CW] Class-2 SAS / call-waiting tone on subscriber loop", "RING")
        _ilog("[CW] Distinctive alerting presented toward client modem", "SYS")
        return

    if tag == "line_retrain":
        if _need_online():
            return
        with _state.lock:
            _state.pending_retrainFX = True
        _clog("[V.34] Speed / pre-emphasis retrain requested (+MS)", "SYS")
        return

    if tag == "isp_degrade":
        _scheme_noise_mult = min(5.0, _scheme_noise_mult + 0.85)
        _scheme_jitter_mult = min(4.0, _scheme_jitter_mult + 0.35)
        _ilog("[NAS] Artificial impairment  --  noise + jitter boosted", "SYS")
        _clog("[ISP] Line quality degraded from head-end", "SYS")
        return

    if tag == "isp_noise":
        with _state.lock:
            _state.isp_upstream_noise = not _state.isp_upstream_noise
            on = _state.isp_upstream_noise
        _ilog(f"[NAS] Upstream noise injection  {'ENABLED' if on else 'DISABLED'}", "SYS")
        return

    if tag == "isp_throttle":
        with _state.lock:
            _state.throttle_bps = 28800
        _clog("[QoS] Effective rate capped at 28800 bps (subscriber policy)", "SYS")
        _ilog("[NAS] Policer applied  --  28.8k shaping", "SYS")
        return

    if tag == "isp_clear_throttle":
        with _state.lock:
            _state.throttle_bps = None
        _clog("[QoS] Bandwidth cap cleared  --  full negotiated rate", "SYS")
        _ilog("[NAS] Policer removed", "SYS")
        return

    if tag == "isp_latency":
        with _state.lock:
            _state.extra_latency_ms = min(2600, _state.extra_latency_ms + 240)
            lat = _state.extra_latency_ms
        _ilog(f"[QoS] Extra shaping RTT +240ms  (total add ~{lat}ms)", "SYS")
        return

    if tag == "isp_ripoff_shrink":
        with _state.lock:
            current = _state.isp_ripoff_mult
        # Build factor options, only showing those that would produce a result >= 0.1
        # and would actually lower the current value.
        candidates = [
            ("0.9",  "Slight squeeze   (x0.9  of current)"),
            ("0.75", "Noticeable cut   (x0.75 of current)"),
            ("0.5",  "Halved           (x0.5  of current)"),
            ("0.25", "Throttled hard   (x0.25 of current)"),
            ("0.1",  "Near-zero        (x0.1  of current  -- floor)"),
        ]
        options = [
            (fid, lbl)
            for fid, lbl in candidates
            if round(current * float(fid), 4) >= 0.1
        ]
        if not options:
            _show_modal(
                "Pipe already at minimum",
                f"Current factor is ~{current:.2f}.  Cannot shrink further (floor: 0.1).",
            )
            return
        _show_modal_choice(
            "SHRINK PIPE  --  choose factor",
            f"Current throughput factor: ~{current:.2f}.  Select the new multiplier:",
            options,
            context="isp_shrink",
        )
        return

    if tag == "isp_dns_hijack":
        with _state.lock:
            _state.isp_dns_hijack = not _state.isp_dns_hijack
            on = _state.isp_dns_hijack
        _ilog(f"[DNS] 'Value added' redirection  {'ENABLED' if on else 'disabled'}", "SYS")
        return

    if tag == "isp_ad_inject":
        with _state.lock:
            _state.isp_ad_inject = not _state.isp_ad_inject
            on = _state.isp_ad_inject
        _ilog(f"[ADWALL] interstitial injector  {'ON' if on else 'OFF'}", "SYS")
        return

    if tag == "isp_surge_toggle":
        with _state.lock:
            _state.isp_surge_billing = not _state.isp_surge_billing
            on = _state.isp_surge_billing
        _ilog(f"[BILLING] surge pricing notices  {'ENABLED' if on else 'disabled'}", "SYS")
        return

    if tag == "isp_fake_tos_spam":
        for i in range(3):
            _ilog(f"[LEGAL] ToS emendation packet #{i+1}  --  deemed accepted", "SYS")
            _clog(f"email: Re: your eternal agreement (ref #{42000+i})", "FAIL")
        return

    if tag == "cust_placebo_boost":
        with _state.lock:
            _state.cust_fightback = min(0.48, round(_state.cust_fightback + 0.12, 4))
            v = _state.cust_fightback
        _clog(f"[+] Software compressor 'MAX'  (+{v:.2f} placebo units)", "OK")
        return

    if tag == "cust_ftc_complaint":
        with _state.lock:
            _state.isp_ripoff_mult = min(1.0, round(_state.isp_ripoff_mult * 1.09 + 0.03, 4))
            m = _state.isp_ripoff_mult
        _clog("[FTC] mailed certified letter  + posted on rec.telecom", "SYS")
        _ilog(f"[FTC] regulatory theater  --  easing factor to ~{m:.2f}", "SYS")
        return

    if tag == "cust_modem_lawyer":
        with _state.lock:
            _state.isp_ripoff_mult = min(1.0, round(_state.isp_ripoff_mult + 0.16, 4))
            m = _state.isp_ripoff_mult
        _clog("[COUNSEL] modem retained counsel  --  demand letter sent", "OK")
        _ilog(f"[LEGAL] settlement class speed restore  ~{m:.2f}", "SYS")
        return

    if tag == "cust_demo_floppy_redial":
        if _need_online():
            return
        with _state.lock:
            _state.demo_disk_redial_pending = True
            _state.overlay = None
        _clog("[DISK] User queued  eject + new demo volume  + full retrain", "SYS")
        return

    if tag == "cust_phone_pickup_joke":
        if _need_online():
            return
        _show_modal_choice(
            "PHONE PICKUP",
            "Someone else just picked up your line. What do you tell them?",
            [
                ("allow_pickup", "Let them pick up the phone"),
                ("stop_pickup", "Tell them to stop picking up"),
            ],
        )
        return

    if tag in ("force_disconnect", "isp_disconnect", "isp_reset_port", "reset_at"):
        with _state.lock:
            _state.overlay = None
        if ls == "ONLINE":
            with _state.lock:
                _state.inject_disconnect = True
                _state.inject_forced_reason = tag
        else:
            with _state.lock:
                _state.dial_abort = True
        return

def render_overlay(stdscr, my: int, mx: int, snap: dict, frame: int):
    """Draw the modem control overlay on top of the main view."""
    side = snap.get('overlay')
    if not side: return
    sel  = snap.get('overlay_sel', 0)

    actions = _OVERLAY_CUST_ACTIONS if side == 'C' else _OVERLAY_ISP_ACTIONS
    title   = "CUSTOMER MODEM CONTROL" if side == 'C' else "ISP MODEM CONTROL"
    col     = _CC if side == 'C' else _CB

    ov_h = len(actions) + 5
    ov_w = min(62, mx - 4)          # never wider than terminal
    ov_y = max(1, (my - ov_h) // 2)
    ov_x = max(0, (mx - ov_w) // 2)

    # Clamp box to terminal bounds
    ov_h = min(ov_h, my - ov_y - 1)
    if ov_h < 3 or ov_w < 8: return   # too small to draw

    inner_w = ov_w - 4   # usable text width inside border + padding

    # Clear background of overlay area (prevents ghost content / black boxes)
    blank = ' ' * ov_w
    for r in range(ov_h):
        row = ov_y + r
        if 0 <= row < my:
            _sa(stdscr, row, ov_x, blank, curses.color_pair(_CW))

    # Box
    _box(stdscr, ov_y, ov_x, ov_h, ov_w, col, title)
    _sa(stdscr, ov_y + 1, ov_x + 2,
        "↑↓ move  Enter apply  Esc/X close"[:inner_w],
        curses.color_pair(_CW))
    _sa(stdscr, ov_y + 2, ov_x + 2, "─" * inner_w, curses.color_pair(col))

    for i, (lbl, _action) in enumerate(actions):
        row = ov_y + 3 + i
        if row >= ov_y + ov_h - 2: break   # don't draw into footer
        hl   = (i == sel)
        attr = curses.color_pair(col) | curses.A_BOLD | curses.A_REVERSE if hl \
               else curses.color_pair(_CW)
        cur  = "▶ " if hl else "  "
        line = f"{cur}{lbl}"[:inner_w].ljust(inner_w)
        _sa(stdscr, row, ov_x + 2, line, attr)

    sep_row = ov_y + ov_h - 2
    if 0 <= sep_row < my:
        _sa(stdscr, sep_row, ov_x + 2, "─" * inner_w, curses.color_pair(col))


def render_modal(stdscr, my: int, mx: int, snap: dict):
    """Blocking-style notice / choice. Dismiss/apply via keys."""
    title = snap.get("modal_title")
    msg   = snap.get("modal_message")
    kind  = snap.get("modal_kind")
    opts  = snap.get("modal_options", [])
    sel   = snap.get("modal_sel", 0)
    if not title or msg is None:
        return

    box_w = min(max(len(title), len(msg), 32) + 10, 60, mx - 4)
    if kind == "choice" and opts:
        box_h = 9 + min(3, len(opts))
    else:
        box_h = 7

    oy = max(1, (my - box_h) // 2)
    ox = max(0, (mx - box_w) // 2)
    blank = " " * box_w
    for r in range(box_h):
        row = oy + r
        if 0 <= row < my:
            _sa(stdscr, row, ox, blank, curses.color_pair(_CW))

    _box(stdscr, oy, ox, box_h, box_w, _CM, title[: box_w - 4])
    inner = box_w - 4

    wrap = msg[: inner * 3]
    _sa(stdscr, oy + 2, ox + 2, wrap[:inner].ljust(inner), curses.color_pair(_CW))
    if len(wrap) > inner:
        _sa(
            stdscr,
            oy + 3,
            ox + 2,
            wrap[inner : inner * 2][:inner].ljust(inner),
            curses.color_pair(_CW),
        )

    if kind == "choice" and opts:
        # Options start below the message lines.
        opt_y = oy + 4
        for i, opt in enumerate(opts[:4]):
            opt_id, opt_lbl = opt
            if opt_y + i >= oy + box_h - 2:
                break
            hl = i == sel
            attr = curses.color_pair(_CC) | curses.A_BOLD | curses.A_REVERSE if hl else curses.color_pair(_CW)
            cur = "▶ " if hl else "  "
            line = f"{cur}{opt_lbl}"[:inner].ljust(inner)
            _sa(stdscr, opt_y + i, ox + 2, line, attr)

        hint = "Enter apply  Esc cancel"
    else:
        hint = "OK [Enter]"

    _sa(
        stdscr,
        oy + box_h - 2,
        ox + 2,
        hint[: inner].ljust(inner),
        curses.color_pair(_CW) | curses.A_BOLD | curses.A_REVERSE,
    )


# ─────────────────────────────────────────────────────────────────────────────
# MAIN RENDER LOOP
# ─────────────────────────────────────────────────────────────────────────────

def main_loop(stdscr):
    global _vol
    _init_colours()
    curses.curs_set(0)
    stdscr.nodelay(True)
    stdscr.timeout(80)          # ~12 fps -- smooth enough, less CPU/TTY pressure
    # Enable mouse so scroll events arrive as KEY_MOUSE rather than raw
    # escape bytes.  Without this, terminals like COSMIC emit ESC (27)
    # for scroll-wheel events which incorrectly triggers the quit handler.
    curses.mousemask(curses.ALL_MOUSE_EVENTS | curses.REPORT_MOUSE_POSITION)
    stdscr.keypad(True)

    # ── Layout -- computed once, never changes mid-session ─────────────────
    my, mx  = stdscr.getmaxyx()
    PHONE_H = 12
    MID_H   = max(16, my - PHONE_H)   # no gap row between panels
    HALF_W  = mx // 2
    R_W     = mx - HALF_W
    BOT_Y   = MID_H                    # bottom panel starts immediately below

    # Three independent windows (curses diffs each against its shadow buffer)
    w_cust = curses.newwin(MID_H, HALF_W, 0, 0)
    w_isp  = curses.newwin(MID_H, R_W, 0, HALF_W)
    w_line = curses.newwin(PHONE_H, mx, BOT_Y, 0)

    stdscr.erase()
    stdscr.noutrefresh()

    frame          = 0
    scroll_cust    = 0   # lines scrolled up in customer log (0 = live tail)
    scroll_isp     = 0   # lines scrolled up in ISP log

    while True:
        key = stdscr.getch()
        with _state.lock:
            _modal_on = _state.modal_title is not None

        if _modal_on:
            snap = _snapshot()
            kind = snap.get("modal_kind")
            if key in (ord('q'), ord('Q')):
                with _state.lock:
                    _state.quit = True
            elif kind == "choice":
                opts = snap.get("modal_options", [])
                sel = snap.get("modal_sel", 0)
                if key == curses.KEY_UP:
                    with _state.lock:
                        _state.modal_sel = max(0, _state.modal_sel - 1)
                elif key == curses.KEY_DOWN:
                    with _state.lock:
                        _state.modal_sel = min(max(0, len(_state.modal_options) - 1), _state.modal_sel + 1)
                elif key in (27, ord('x'), ord('X')):  # Esc or X cancel
                    _clear_modal()
                elif key in (10, 13, curses.KEY_ENTER):
                    if opts and 0 <= sel < len(opts):
                        opt_id, _ = opts[sel]
                        ctx = snap.get("modal_context")
                        if ctx == "isp_shrink":
                            _apply_isp_shrink_choice(opt_id)
                        else:  # default: phone_pickup
                            _apply_phone_pickup_choice(opt_id)
                    _clear_modal()
            else:
                if key in (10, 13, curses.KEY_ENTER):
                    _clear_modal()
                elif key in (27, ord('x'), ord('X')):
                    _clear_modal()

            _log_h = max(1, MID_H - WAVE_ROWS - 4)
            scroll_cust = min(scroll_cust, max(0, len(snap['customer']['log']) - _log_h))
            scroll_isp = min(scroll_isp, max(0, len(snap['isp']['log']) - _log_h))
            if snap['vol_flash'] > 0:
                with _state.lock:
                    _state.vol_flash = max(0, _state.vol_flash - 1)
            render_modem(w_cust, MID_H, HALF_W, snap['customer'], _CC, frame, scroll_cust)
            render_modem(w_isp, MID_H, R_W, snap['isp'], _CB, frame, scroll_isp)
            render_line(w_line, PHONE_H, mx, snap, frame)
            render_modal(stdscr, my, mx, snap)
            w_cust.noutrefresh()
            w_isp.noutrefresh()
            w_line.noutrefresh()
            stdscr.noutrefresh()
            curses.doupdate()
            frame += 1
            time.sleep(0.08)
            continue

        if key in (ord('q'), ord('Q')):
            with _state.lock: _state.quit = True
        # Volume: +/= and ] raise; -/[ lower.
        # ] and [ are shift-free alternatives for terminals (e.g. XFCE4) that
        # intercept shifted keys or map +/- to font-size shortcuts in keypad mode.
        if key in (ord('+'), ord('='), ord(']')):
            _vol = min(_vol_max, round(_vol + _vol_step, 1))
            with _state.lock: _state.vol_flash = 8
        if key in (ord('-'), ord('[')):
            _vol = max(_vol_min, round(_vol - _vol_step, 1))
            with _state.lock: _state.vol_flash = 8
        if key in (ord('d'), ord('D')):
            with _state.lock: _state.debug = not _state.debug
        # ── Overlay controls ──────────────────────────────────────────────
        snap_ov = _state.overlay   # read without lock (single assign is atomic)
        if snap_ov:  # overlay is open -- intercept nav keys
            actions_len = (len(_OVERLAY_CUST_ACTIONS) if snap_ov == 'C'
                           else len(_OVERLAY_ISP_ACTIONS))
            if key == curses.KEY_UP:
                with _state.lock:
                    _state.overlay_sel = max(0, _state.overlay_sel - 1)
            elif key == curses.KEY_DOWN:
                with _state.lock:
                    _state.overlay_sel = min(actions_len - 1, _state.overlay_sel + 1)
            elif key in (10, 13, curses.KEY_ENTER):
                actions = (_OVERLAY_CUST_ACTIONS if snap_ov == 'C'
                           else _OVERLAY_ISP_ACTIONS)
                with _state.lock:
                    sel_action = actions[_state.overlay_sel][1]
                _apply_overlay_action(sel_action)
            elif key in (27, ord('x'), ord('X')):  # Esc or X closes overlay
                with _state.lock: _state.overlay = None
        # C/I overlay toggle always active (works whether overlay is open or not)
        if key in (ord('c'), ord('C')):
            with _state.lock:
                _state.overlay = None if _state.overlay == 'C' else 'C'
                _state.overlay_sel = 0
        elif key in (ord('i'), ord('I')):
            with _state.lock:
                _state.overlay = None if _state.overlay == 'I' else 'I'
                _state.overlay_sel = 0
        if not snap_ov:  # W only works when no overlay open
            if key in (ord('w'), ord('W')):
                # Launch page-load simulation
                url = random.choice(_FAKE_URLS)
                with _state.lock:
                    online = _state.line_state == 'ONLINE'
                    busy = _state.page_load_active
                if online and not busy:
                    with _state.lock:
                        _state.page_load_active = True
                        _state.page_load_url = url
                        _state.page_load_stage = 'starting...'
                        _state.page_load_progress = 0.0
                    threading.Thread(target=_page_load_worker,
                                     args=(url,),
                                     daemon=True).start()
                elif busy:
                    _show_modal("Page load running",
                                "Wait for the current HTTP transfer to finish.")
                else:
                    _show_modal("Not connected",
                                "Page load needs an active PPP link. Wait for CONNECT.")
        # PAGE UP / PAGE DOWN: fallback scroll (no overlay needed)
        if key == curses.KEY_PPAGE and not snap_ov:
            scroll_cust = min(scroll_cust + 3, 9999)
        if key == curses.KEY_NPAGE and not snap_ov:
            scroll_cust = max(0, scroll_cust - 3)
        if key == curses.KEY_MOUSE:
            try:
                _, mx_pos, _, _, bstate = curses.getmouse()
                # Scroll up (BUTTON4) or down (BUTTON5)
                # Route to the pane the cursor is in (left = customer, right = ISP)
                if bstate & curses.BUTTON4_PRESSED:   # wheel up = older history
                    if mx_pos < HALF_W: scroll_cust = min(scroll_cust + 3, 9999)
                    else:               scroll_isp  = min(scroll_isp  + 3, 9999)
                elif bstate & curses.BUTTON5_PRESSED: # wheel down = newer
                    if mx_pos < HALF_W: scroll_cust = max(0, scroll_cust - 3)
                    else:               scroll_isp  = max(0, scroll_isp  - 3)
            except curses.error:
                pass

        snap = _snapshot()

        # Clamp scroll offsets to actual log length so scrolling stops at top
        _log_h = max(1, MID_H - WAVE_ROWS - 4)
        scroll_cust = min(scroll_cust, max(0, len(snap['customer']['log']) - _log_h))
        scroll_isp  = min(scroll_isp,  max(0, len(snap['isp']['log'])      - _log_h))

        # Decay vol flash counter
        if snap['vol_flash'] > 0:
            with _state.lock:
                _state.vol_flash = max(0, _state.vol_flash - 1)

        render_modem(w_cust, MID_H, HALF_W, snap['customer'], _CC, frame, scroll_cust)
        render_modem(w_isp,  MID_H, R_W,    snap['isp'],      _CB, frame, scroll_isp)
        render_line (w_line, PHONE_H, mx,   snap, frame)

        if snap['done']:
            _audio.silence()   # drain queue + close stdin; no SIGCHLD fired here
            msg  = "  Session ended.  Press any key to exit.  "
            msg_y = my // 2
            msg_x = max(0, (mx - len(msg)) // 2)
            _sa(stdscr, msg_y, msg_x, msg,
                curses.color_pair(_CW) | curses.A_REVERSE | curses.A_BOLD)
            w_cust.noutrefresh()
            w_isp.noutrefresh()
            w_line.noutrefresh()
            stdscr.noutrefresh()
            curses.doupdate()
            stdscr.nodelay(False)
            stdscr.getch()
            _audio.stop()   # aplay already exiting; join thread, final cleanup
            break

        w_cust.noutrefresh()
        w_isp.noutrefresh()
        w_line.noutrefresh()
        # Draw overlay on top of everything (uses stdscr coords)
        render_overlay(stdscr, my, mx, snap, frame)
        render_modal(stdscr, my, mx, snap)
        stdscr.noutrefresh()
        curses.doupdate()       # single terminal write -- no blink

        frame += 1
        time.sleep(0.08)

    _audio.stop()


# ─────────────────────────────────────────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────────────────────────────────────────

def run(stdscr):
    global _state, _audio
    _audio = AudioPlayer()
    _audio.start()

    # Show startup menu
    result = startup_menu(stdscr)
    if result[0] is None:
        _audio.stop()
        return
    (prof_idx, fail_idx, num_idx, max_attempts, debug,
     sc_weights, snd_idx, ml_count, ml_mode, custom_num) = result

    _CUSTOM_NUM_IDX = len(ISP_NUMBERS) - 1
    profile    = PROFILES[prof_idx]
    fail_prob  = FAIL_OPTIONS[fail_idx][1]
    if num_idx == _CUSTOM_NUM_IDX:
        isp_number = custom_num if custom_num.strip() else ISP_NUMBERS[_CUSTOM_NUM_IDX][0]
        isp_label  = "custom"
    else:
        isp_number, isp_lbl_full = ISP_NUMBERS[num_idx]
        isp_label  = isp_lbl_full.split("--")[0].strip()

    _state = UIState(profile, fail_prob,
                     isp_number=isp_number, isp_label=isp_label,
                     debug=debug, max_attempts=max_attempts,
                     scenario_weights=sc_weights,
                     sound_scheme_idx=snd_idx,
                     ml_count=ml_count, ml_mode=ml_mode)

    seq = threading.Thread(target=sequencer, daemon=True)
    seq.start()

    main_loop(stdscr)


if __name__ == "__main__":
    try:
        curses.wrapper(run)
    except KeyboardInterrupt:
        pass