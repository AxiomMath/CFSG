module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3U43
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43
  CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] def rhoArr : Array ℕ := Array.ofFn (n := 820) fun i => ptIndex (semiFun (decode i))

@[expose] def bad16 (v : List (Array ℕ)) : Bool :=
  fixB baseArr.toList v 16 && !fixB baseArr.toList v 8

@[expose] def rhoOK : Bool :=
  isInvA 820 rhoArr (invCand 820 rhoArr) &&
    inP (compA 820 rhoArr (compA 820 tabA (invCand 820 rhoArr))) &&
    inP (compA 820 rhoArr (compA 820 tabB (invCand 820 rhoArr))) &&
    inP (compA 820 rhoArr rhoArr)

@[expose] def countBadP : ℕ := countW bad16 blocks []

@[expose] def countBadRho : ℕ := countW (fun w => bad16 (rhoArr :: w)) blocks []

end CFSG.EvenSporadicStandard.Fin76b
