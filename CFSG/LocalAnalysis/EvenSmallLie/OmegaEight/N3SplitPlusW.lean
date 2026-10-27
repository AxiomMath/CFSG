module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitPlusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitWit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitNCData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitRoots
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Wit

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split CFSG.EvenSmallLie.OmegaEight.N3Split.Plus

structure Wit where
  cE : Enum
  tcE : Enum
  ukE : Enum
  c2E : Enum
  p3E : Enum
  sE0 : Enum
  mE0 : Enum
  s2E : Enum
  m2E : Enum
  sE1 : Enum
  mE1 : Enum
  imgX : ℕ → ℕ
  lin : ℕ → ℕ → List (List ℕ) × List ℕ × List ℕ
  ncLin : List (List ℕ) × List ℕ × List ℕ
  cls0 : (ℕ → List ℕ) × (ℕ → ℕ) × (ℕ → ℕ)
  cls2 : (ℕ → List ℕ) × (ℕ → ℕ) × (ℕ → ℕ)
  cls1 : (ℕ → List ℕ) × (ℕ → ℕ) × (ℕ → ℕ)

@[expose] def tuples (W : Wit) : List (List ℕ) :=
  (W.p3E.keys.toList.filter (· != idK)).map fun z => [z]

@[expose] def cCheck (W : Wit) : Bool := enumOK cGens W.cE && W.cE.keys.size == 80640

@[expose] def tcCheck (W : Wit) : Bool :=
  enumOK tGens W.tcE && W.tcE.keys.size == 256 && gensIn tGens W.cE &&
    centerCheck tGens W.tcE [idK, phiK, bK, mulK phiK bK] && commGens tGens phiK &&
    commGens tGens bK && memK W.tcE.keys bK

@[expose] def ukCheck (W : Wit) : Bool :=
  enumOK ukGens W.ukE && W.ukE.keys.size == 128 && gensIn ukGens W.tcE &&
    avoidCheck W.tcE W.ukE

@[expose] def m2Check (W : Wit) : Bool :=
  allRootsF 256 (invsOf W.tcE.keys) ((List.range 4096).filter fun v => mulVecK phiK v == v)

@[expose] def offCheck (W : Wit) : Bool := allRootsF 2048 (invsOf W.tcE.keys) (List.range 4096)

@[expose] def phiCheck (W : Wit) : Bool :=
  fixCount phiK == 64 && imgCheckW phiK W.imgX && invPair phiK phiK && phiK != idK &&
    bK != idK && bK != phiK && mulK bK bK == idK && mulK bK phiK == mulK phiK bK &&
    commGens cGens phiK

@[expose] def c2Check (W : Wit) : Bool :=
  enumOK c2Gens W.c2E && W.c2E.keys.size == 768 && gensIn c2Gens W.cE &&
    commGens c2Gens phiK && commGens c2Gens bK && centInCheck W.cE bK W.c2E &&
    W.c2E.keys.all fun c => fpowK c 1152 == idK

@[expose] def p3Check (W : Wit) : Bool :=
  enumOK p3Gens W.p3E && W.p3E.keys.size == 3 && gensIn p3Gens W.c2E

@[expose] def candChk (W : Wit) : Bool :=
  candCheckW W.cE W.c2E samples reps ys (tuples W) cases W.lin &&
    reps.all (fun r => invPair r.1 r.2) && samples.all (memK W.c2E.keys)

@[expose] def brayChk (W : Wit) (i : ℕ) (prog : List (ℕ × ℕ × ℕ)) (out : ℕ) : Bool :=
  brayCheck (base i) prog out phiK W.cE

@[expose] def sChk0 (W : Wit) : Bool :=
  gensOK (base 0) && gensOK sGens0 && enumOK sGens0 W.sE0 &&
    W.sE0.keys.size == 16384 && gensIn tGens W.sE0 &&
    classCertW W.sE0 sReps0 [phiK, tauK] W.cls0.1 W.cls0.2.1 W.cls0.2.2 &&
    enumOK mGens0 W.mE0 &&
    W.mE0.keys.size == 8192 && gensIn mGens0 W.sE0 &&
    [phiK, tauK].all fun r => !(memK W.mE0.keys r) && decide (r < 2 ^ 144)

@[expose] def tauChk0 (W : Wit) : Bool :=
  memK W.sE0.keys tauK && commCount W.sE0 tauK == 256 && fixCount tauK == 64 &&
    kerCount W.sE0 tauK == 2 && invPair tauK tauK

@[expose] def s2Chk (W : Wit) : Bool :=
  gensOK s2Gens && enumOK s2Gens W.s2E && W.s2E.keys.size == 32768 && gensIn tGens W.s2E &&
    classCertW W.s2E s2Reps [phiK] W.cls2.1 W.cls2.2.1 W.cls2.2.2 && enumOK m2Gens W.m2E &&
    W.m2E.keys.size == 16384 &&
    gensIn m2Gens W.s2E && [phiK].all fun r => !(memK W.m2E.keys r) && decide (r < 2 ^ 144)

@[expose] def sChk1 (W : Wit) : Bool :=
  gensOK (base 1) && gensOK sGens1 && enumOK sGens1 W.sE1 &&
    W.sE1.keys.size == 16384 && gensIn tGens W.sE1 &&
    classCertW W.sE1 sReps1 [phiK, tauK] W.cls1.1 W.cls1.2.1 W.cls1.2.2 &&
    enumOK mGens1 W.mE1 &&
    W.mE1.keys.size == 8192 && gensIn mGens1 W.sE1 &&
    [phiK, tauK].all fun r => !(memK W.mE1.keys r) && decide (r < 2 ^ 144)

@[expose] def tauChk1 (W : Wit) : Bool :=
  memK W.sE1.keys tauK && commCount W.sE1 tauK == 256 && fixCount tauK == 64 &&
    kerCount W.sE1 tauK == 2 && invPair tauK tauK

@[expose] def noChk (W : Wit) : Bool := W.cE.keys.all fun c => fpowK c 9 != idK || fpowK c 3 == idK

@[expose] def ncChk (W : Wit) : Bool :=
  ((List.range W.cE.keys.size).all fun i =>
      mulK (W.cE.keys.getD i 0) (W.cE.keys.getD i 0) != idK || W.cE.keys.getD i 0 == idK ||
        fixCountF (W.cE.keys.getD i 0) != 1024 || reflList.contains (W.cE.keys.getD i 0)) &&
    (coxList.all fun ρ => invPair ρ ρ && memK W.cE.keys ρ && fixCountF ρ == 1024) &&
    chainAux W.cE.keys reflList [] coxList chainList &&
    linCheckWith (commCons coxList) W.ncLin.1 W.ncLin.2.1 W.ncLin.2.2 &&
    spanAll W.ncLin.2.1 W.ncLin.2.2.length
      (fun m => m == 0 || m == idK || m == phiK || m == (idK ^^^ phiK)) &&
    mulK (idK ^^^ phiK) (idK ^^^ phiK) == 0 && memK W.cE.keys phiK

end CFSG.EvenSmallLie.OmegaEight.N3Split.PlusW
