module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKsData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] def vIxL : List ℕ := [0, 2, 5, 7]

@[expose] def ord8W (bs : List ℕ) (t : Array ℕ) (w : List (Array ℕ)) : Bool :=
  fixB bs (t :: w) 8 && !fixB bs (t :: w) 4

@[expose] def centKs (r : Array ℕ) : ℕ :=
  vIxL.foldl (fun c k => c + countW (commW (tArr k) [r]) blocks []) 0

@[expose] def ks8Check (_ : Unit := ()) : Bool :=
  (List.range 8).all fun j =>
    isInvA 820 ks8Reps[j]! (invCand 820 ks8Reps[j]!) &&
      inP (compA 820 ks8Reps[j]! (invCand 820 (tArr ks8Coset[j]!))) &&
      eqA 820 (powA 820 ks8Reps[j]! 8) (idA 820) &&
      !eqA 820 (powA 820 ks8Reps[j]! 4) (idA 820) && centKs ks8Reps[j]! == ks8Cent[j]!

@[expose] def ks8Counts (_ : Unit := ()) : Bool :=
  (List.range 4).all fun i => countW (ord8W baseArr.toList (tArr vIxL[i]!)) blocks [] == ks8Count[i]!

end CFSG.EvenSporadicStandard.Fin76b.U16
