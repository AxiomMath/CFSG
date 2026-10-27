module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKsCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKs2Data

public section

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.EvenSporadicStandard.M24Std.CU43

@[expose] def invRelW (t v vi : Array ℕ) (w : List (Array ℕ)) : Bool :=
  allLt 820 (fun i => evR (t :: w) (evR (t :: w) i) == i) &&
    allLt 820 (fun i => evR (t :: w) v[i]! == vi[evR (t :: w) i]!)

@[expose] def centKs2 (v ξ : Array ℕ) : ℕ :=
  vIxL.foldl (fun c k => c + countW (commW (tArr k) [v, ξ]) blocks []) 0

@[expose] def u7Check (_ : Unit := ()) : Bool :=
  centKs reps[4]! == 2880 && isInvA 820 y8Arr (invCand 820 y8Arr) && inP y8Arr &&
    eqA 820 (powA 820 y8Arr 8) (idA 820) && !eqA 820 (powA 820 y8Arr 4) (idA 820) &&
    eqA 820 (compA 820 y8Arr reps[4]!) (compA 820 reps[4]! y8Arr)

@[expose] def pairCheck (_ : Unit := ()) : Bool :=
  (List.range 3).all fun i =>
    isInvA 820 xiArrs[i]! (invCand 820 xiArrs[i]!) &&
      eqA 820 (compA 820 xiArrs[i]! xiArrs[i]!) (idA 820) &&
      inP (compA 820 xiArrs[i]! (invCand 820 (tArr 7))) &&
      eqA 820 (compA 820 xiArrs[i]! ks8Reps[5 + i]!)
        (compA 820 (invCand 820 ks8Reps[5 + i]!) xiArrs[i]!) &&
      countW (invRelW (tArr 7) ks8Reps[5 + i]! (invCand 820 ks8Reps[5 + i]!)) blocks [] ==
        pairNum[i]! && centKs2 ks8Reps[5 + i]! xiArrs[i]! == pairCent[i]!

@[expose] def d16Check (_ : Unit := ()) : Bool :=
  isInvA 820 d16A (invCand 820 d16A) && isInvA 820 d16B (invCand 820 d16B) &&
    inP (compA 820 d16A (invCand 820 (tArr 5))) && inP (compA 820 d16B (invCand 820 (tArr 5))) &&
    eqA 820 (powA 820 d16A 8) (idA 820) && !eqA 820 (powA 820 d16A 4) (idA 820) &&
    eqA 820 (compA 820 d16B d16B) (idA 820) &&
    eqA 820 (compA 820 d16B d16A) (compA 820 (invCand 820 d16A) d16B) &&
    (List.range 8).all (fun j => !eqA 820 d16B (powA 820 d16A j)) &&
    [ks8Reps[7]!, xiArrs[2]!].all fun r =>
      eqA 820 (compA 820 d16A r) (compA 820 r d16A) &&
        eqA 820 (compA 820 d16B r) (compA 820 r d16B)

end CFSG.EvenSporadicStandard.Fin76b.U16
