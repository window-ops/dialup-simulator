# Dialup Simulator

**NOTE: THIS PROGRAM HAS BEEN MADE WITH THE ASSISTANCE OF MULTIPLE AIs. THIS PROGRAM WAS TESTED MULTIPLE TIMES DURING DEVELOPMENT.**

Dial-up modem simulator (single file) - local two-sided V.90 / ISDN simulation.

This program is intended to run on Linux only. It uses the terminal curses API and spawns ALSA 'aplay' via subprocess for real-time PCM; paths and utilities are not abstracted for Windows or macOS. Making it cross-platform would require a different audio sink (native APIs or a portable library), TUI adjustments, and validation on those OSes.

## Requirements
- Python 3.6 or newer.
- Standard library only (no pip packages).
- Recommended: alsa-utils package with 'aplay' on PATH for audible handshake and carrier output. If aplay is missing, the emulator still runs with timing and logs in sync, but the audio is silent.

**Run:** ``python3 dialup.py``

## What it does
- Split view: customer modem log plus waveform vs ISP server log plus waveform.
- A phone-line strip: phase bar, signal/RX/TX/SNR meters, negotiated rate and byte counts, optional MLPPP link status tiles, fake HTTP lines, and optional page-load progress.
- Analog V.90-style audio: dial tone -> DTMF -> ringback -> CED (2100 Hz plus phase reversals) -> ANSam (15 Hz AM) -> optional USR bong -> V.21 FSK -> profile-specific V.34/V.90 negotiation (multi-tone bursts and sweeps) -> steady carrier while online.
- ISDN TA paths (BRI 64k, BRI 128k with MLPPP, PRI): shorter digital-style phases (Q.931 / LAPD / PPP flavour), quieter than analog.
- Modem profiles with distinct timbre and timing: USRobotics Sportster 56K, Hayes Optima 56K, Zoom 56K (budget), Motorola ModemSURFR 56K.
- Failure injection on analog attempts (random training scenarios and redial) with configurable max attempts and optional per-scenario weights.
- Sound schemes (noisy line, clean DSP, retro 28.8k, silent, etc.) scale synthesis noise and jitter from the startup menu.
- MLPPP (1-20 links): simultaneous vs serial bonding; each extra link dials and trains with per-link tone detuning; a synthetic multilink LCP / IPCP burst after all links are up; aggregate bps tracked for simulation and UI.

## Startup menu
Pick modem, failure rate, ISP listing, retry budget, optional advanced failure weights, sound scheme, and MLPPP count / bonding mode.

**Keys:** arrows, Tab / Shift-Tab, Space toggles accordions, Enter confirms and connects, + / - or ] / [ volume, D debug, Q / Esc exit.

## Main session (connected and dialling UI)

| Key          | Action                                              |
|--------------|-----------------------------------------------------|
| Q            | Quit / end session                                  |
| + / - ] / [  | Playback volume (global PCM scaler)                 |
| D            | Toggle debug strip on the phone line panel          |
| W            | Fake HTTP page load over PPP (only when ONLINE)     |
| C / I        | Customer or ISP control overlay (toggle)            |
| PgUp / PgDn  | Scroll customer log                                 |
| Mouse wheel  | Scroll the log under the pointer (left = customer, right = ISP) |

**In overlays:** Up/Down move, Enter runs the selected action, Esc / X closes.  
Speaker, noise, shaping, caps, latency, call-waiting, and similar actions apply during dialling where meaningful. Forced hang-up / ATZ / NAS-style actions raise DialAbort while not yet ONLINE. Actions that need a finished link (e.g. +MS retrain) open an error modal.

**Customer actions include:** line noise toggle, speaker mute (relay click), ATH / ATZ (abort dial or drop when up), call-waiting beep, line retrain when connected.

**ISP actions include:** force client disconnect, NAS port reset, line degrade (noise plus jitter), upstream noise toggle, 28.8k rate cap, clear cap, additive shaper latency.

## Implementation notes
- A sequencer thread drives the call (dial, negotiate, MLPPP, online loop, hang-up); the curses UI runs on the main thread.
- Audio is mono S16LE at 8 kHz, written to aplay if available. pack() applies volume, optional scheme silence, speaker path mute, and line-quality mixes so operator toggles affect all queued audio, including mid-dial DTMF and ringing.