module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2WitSecond
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Wit

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.Minus

structure Wit where
  cE : Enum
  tcE : Enum
  uE : Enum
  c2E : Enum
  p3E : Enum
  sE0 : Enum
  mE0 : Enum
  sE1 : Enum
  mE1 : Enum
  sE7 : Enum
  mE7 : Enum
  uB : ℕ → List ℕ
  imgX : ℕ → ℕ
  lin : ℕ → ℕ → List (List ℕ) × List ℕ × List ℕ
  sB0 : ℕ → List ℕ
  sY0 : ℕ → ℕ
  sB1 : ℕ → List ℕ
  sY1 : ℕ → ℕ
  sB7 : ℕ → List ℕ
  sY7 : ℕ → ℕ
  sZ7 : ℕ → ℕ
  mB7 : ℕ → List ℕ

@[expose] def tuples (W : Wit) : List (List ℕ) :=
  (W.p3E.keys.toList.filter (· != idK)).flatMap fun z₁ =>
    (W.p3E.keys.toList.filter fun z₂ => z₂ != idK && z₂ != z₁ && z₂ != mulK z₁ z₁).map
      fun z₂ => [z₁, z₂]

@[expose] def cCheck (W : Wit) : Bool := enumOK cGensMinus W.cE && W.cE.keys.size == 51840

@[expose] def tcCheck (W : Wit) : Bool :=
  enumOK tGensMinus W.tcE && W.tcE.keys.size == 128 && gensIn tGensMinus W.cE &&
    centerCheck tGensMinus W.tcE [idK, phiK, bK, mulK phiK bK] && commGens tGensMinus phiK &&
    commGens tGensMinus bK && memK W.tcE.keys bK

@[expose] def uCheck (W : Wit) : Bool :=
  enumOK uGens W.uE && W.uE.keys.size == 64 && gensIn uGens W.tcE && invFixCheckW W.uE 8 W.uB

@[expose] def m2Check (W : Wit) : Bool :=
  allRoots 128 (invsOf W.tcE.keys) ((List.range 4096).filter fun v => mulVecK phiK v == v)

@[expose] def offCheck (W : Wit) : Bool := allRoots 2048 (invsOf W.tcE.keys) (List.range 4096)

@[expose] def phiCheck (W : Wit) : Bool :=
  decide (fixCount phiK ≤ 128) && imgCheckW phiK W.imgX && invPair phiK phiK && phiK != idK &&
    bK != idK && bK != phiK && mulK bK bK == idK && mulK bK phiK == mulK phiK bK &&
    commGens cGensMinus phiK

@[expose] def c2Check (W : Wit) : Bool :=
  enumOK c2Gens W.c2E && W.c2E.keys.size == 1152 && gensIn c2Gens W.cE &&
    commGens c2Gens phiK && commGens c2Gens bK && centInCheck W.cE bK W.c2E

@[expose] def p3Check (W : Wit) : Bool :=
  enumOK p3Gens W.p3E && W.p3E.keys.size == 9 && gensIn p3Gens W.c2E &&
    ys == [(genK p3Gens 0).1, (genK p3Gens 1).1] && (genK p3Gens 0).1 != idK &&
    (genK p3Gens 1).1 != idK && (genK p3Gens 1).1 != (genK p3Gens 0).1 &&
    (genK p3Gens 1).1 != mulK (genK p3Gens 0).1 (genK p3Gens 0).1

@[expose] def candChk (W : Wit) : Bool :=
  candCheckW W.cE W.c2E samples reps ys (tuples W) cases W.lin &&
    reps.all (fun r => invPair r.1 r.2) && samples.all (memK W.c2E.keys)

@[expose] def brayChk (W : Wit) (i : ℕ) (prog : List (ℕ × ℕ × ℕ)) (out : ℕ) : Bool :=
  brayCheck (base i) prog out phiK W.cE

@[expose] def sChk0 (W : Wit) : Bool :=
  gensOK (base 0) && gensOK sGens0 && enumOK sGens0 W.sE0 && W.sE0.keys.size == 8192 &&
    gensIn tGensMinus W.sE0 && oneClassCheckW W.sE0 phiK W.sB0 W.sY0 && enumOK mGens0 W.mE0 &&
    W.mE0.keys.size == 4096 && gensIn mGens0 W.sE0 && !(W.mE0.keys.contains phiK)

@[expose] def sChk1 (W : Wit) : Bool :=
  gensOK (base 1) && gensOK sGens1 && enumOK sGens1 W.sE1 && W.sE1.keys.size == 8192 &&
    gensIn tGensMinus W.sE1 && oneClassCheckW W.sE1 phiK W.sB1 W.sY1 && enumOK mGens1 W.mE1 &&
    W.mE1.keys.size == 4096 && gensIn mGens1 W.sE1 && !(W.mE1.keys.contains phiK)

@[expose] def secondChk (W : Wit) : Bool :=
  gensOK (base 7) && (baseK (base 7)).all (· < 2 ^ 144) && gensOK sGens7 &&
    enumOK sGens7 W.sE7 && W.sE7.keys.size == 256 && gensIn tGensMinus W.sE7 &&
    memK W.sE7.keys tauK && secondCheckW W.sE7 phiK tauK 128 W.sB7 W.sY7 W.sZ7 &&
    mulK zK tauK == mulK tauK zK && fpowK zK 8 == idK && fpowK zK 4 != idK &&
    allRoots 2048 (invsOf W.sE7.keys) (List.range 4096) && enumOK mGens7 W.mE7 &&
    W.mE7.keys.size == 128 && gensIn mGens7 W.sE7 && invFixCheckW W.mE7 8 W.mB7

@[expose] def no8Chk (W : Wit) : Bool := no8Check W.cE

end CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW
