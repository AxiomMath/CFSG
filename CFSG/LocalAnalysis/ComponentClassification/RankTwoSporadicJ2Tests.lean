module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Exc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ComponentClassification.J2Cover

@[expose] def j2InP (t : Array ℕ) : Bool := inP t

@[expose] def j2InR (t : Array ℕ) : Bool := j2InP t || j2InP (compA 315 outerArr t)

@[expose] def j2GensR : Array (Array ℕ) := autStrong.push outerArr

@[expose] def j2PS : List ℕ := [0, 4, 3]

@[expose] def j2Fuel : ℕ := 2 ^ 20

theorem j2PS_lt : ∀ p ∈ j2PS, p < 315 := by decide

@[expose] def j2CheckII (sc sp : String) : Bool :=
  let d := decodeCertR (slpRegs 315 j2GensR (decodePairs sp)) sc
  censusOK 315 j2PS j2Fuel j2InP j2InP false true false d.sGens d.roots d.nodes &&
    (allLt d.sGens.size fun k => j2InP d.sGens[k]! || j2InP (compA 315 outerArr d.sGens[k]!)) &&
    (enumBfs 315 d.sGens j2PS j2Fuel).pts.size == 256

@[expose] def j2CheckExc (e0 : Array (Array ℕ)) (sc sx sp : String) : Bool :=
  let regs := slpRegs 315 j2GensR (decodePairs sp)
  let d := decodeCertR regs sc
  censusExcOK 315 j2PS j2Fuel j2InP j2InP j2InR false false false d.sGens d.roots d.nodes e0
      (decodeExcR regs sx) &&
    (allLt d.sGens.size fun k => j2InP d.sGens[k]! || j2InP (compA 315 outerArr d.sGens[k]!)) &&
    (enumBfs 315 d.sGens j2PS j2Fuel).pts.size == 256

end CFSG.ComponentClassification.RankTwoSporadic.J2
