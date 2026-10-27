module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Wit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2.PlusW

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.Plus

structure Wit where
  cE : Enum
  tcE : Enum
  uE : Enum
  c2E : Enum
  p3E : Enum
  sE4 : Enum
  mE4 : Enum
  sE5 : Enum
  mE5 : Enum
  uB : ℕ → List ℕ
  imgX : ℕ → ℕ
  lin : ℕ → ℕ → List (List ℕ) × List ℕ × List ℕ
  sB4 : ℕ → List ℕ
  sY4 : ℕ → ℕ
  sB5 : ℕ → List ℕ
  sY5 : ℕ → ℕ

@[expose] def tuples (W : Wit) : List (List ℕ) :=
  (W.p3E.keys.toList.filter (· != idK)).map fun z => [z]

@[expose] def cCheck (W : Wit) : Bool := enumOK cGensPlus W.cE && W.cE.keys.size == 40320

@[expose] def tcCheck (W : Wit) : Bool :=
  enumOK tGensPlus W.tcE && W.tcE.keys.size == 128 && gensIn tGensPlus W.cE &&
    centerCheck tGensPlus W.tcE [idK, phiK, bK, mulK phiK bK] && commGens tGensPlus phiK &&
    commGens tGensPlus bK && memK W.tcE.keys bK

@[expose] def uCheck (W : Wit) : Bool :=
  enumOK uGens W.uE && W.uE.keys.size == 64 && gensIn uGens W.tcE && invFixCheckW W.uE 8 W.uB

@[expose] def m2Check (W : Wit) : Bool :=
  allRoots 128 (invsOf W.tcE.keys) ((List.range 4096).filter fun v => mulVecK phiK v == v)

@[expose] def offCheck (W : Wit) : Bool := allRoots 2048 (invsOf W.tcE.keys) (List.range 4096)

@[expose] def phiCheck (W : Wit) : Bool :=
  decide (fixCount phiK ≤ 128) && imgCheckW phiK W.imgX && invPair phiK phiK && phiK != idK &&
    bK != idK && bK != phiK && mulK bK bK == idK && mulK bK phiK == mulK phiK bK &&
    commGens cGensPlus phiK

@[expose] def c2Check (W : Wit) : Bool :=
  enumOK c2Gens W.c2E && W.c2E.keys.size == 384 && gensIn c2Gens W.cE &&
    commGens c2Gens phiK && commGens c2Gens bK && centInCheck W.cE bK W.c2E

@[expose] def p3Check (W : Wit) : Bool :=
  enumOK p3Gens W.p3E && W.p3E.keys.size == 3 && gensIn p3Gens W.c2E

@[expose] def candChk (W : Wit) : Bool :=
  candCheckW W.cE W.c2E samples reps ys (tuples W) cases W.lin &&
    reps.all (fun r => invPair r.1 r.2) && samples.all (memK W.c2E.keys)

@[expose] def brayChk (W : Wit) (i : ℕ) (prog : List (ℕ × ℕ × ℕ)) (out : ℕ) : Bool :=
  brayCheck (base i) prog out phiK W.cE

@[expose] def sChk4 (W : Wit) : Bool :=
  gensOK (base 4) && gensOK sGens4 && enumOK sGens4 W.sE4 && W.sE4.keys.size == 8192 &&
    gensIn tGensPlus W.sE4 && oneClassCheckW W.sE4 phiK W.sB4 W.sY4 && enumOK mGens4 W.mE4 &&
    W.mE4.keys.size == 4096 && gensIn mGens4 W.sE4 && !(W.mE4.keys.contains phiK)

@[expose] def sChk5 (W : Wit) : Bool :=
  gensOK (base 5) && gensOK sGens5 && enumOK sGens5 W.sE5 && W.sE5.keys.size == 8192 &&
    gensIn tGensPlus W.sE5 && oneClassCheckW W.sE5 phiK W.sB5 W.sY5 && enumOK mGens5 W.mE5 &&
    W.mE5.keys.size == 4096 && gensIn mGens5 W.sE5 && !(W.mE5.keys.contains phiK)

end CFSG.EvenSmallLie.OmegaEight.Stage2.PlusW
