module

public import CFSG.Monster.B.TwoA.Census.PermClassesInputs

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Census

@[expose] def sigRec (a : Array ℕ) (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sigRec a w n ^^^ (if w.testBit a[n]! then 2 ^ n else 0)

@[expose] def sigN (a : Array ℕ) (w : ℕ) : ℕ := sigRec a w 24

@[expose] def powSumN (a : Array ℕ) (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => w ^^^ sigN a (powSumN a w k)

@[expose] def eighthImgs (a : Array ℕ) : List ℕ :=
  (List.range 12).map fun i => powSumN a (Bmask i) 8

@[expose] def popTab : Array ℕ := ((List.range 4096).map (popc 12)).toArray

@[expose] def pop24 (x : ℕ) : ℕ := popTab[x % 4096]! + popTab[x / 4096 % 4096]!

@[expose] def badWt (w : ℕ) : ℕ := if w = 0 ∨ w = 16 then 0 else 1

@[expose] def eighthWeightBad (a : Array ℕ) : ℕ :=
  let ims := eighthImgs a
  treeSumN (fun x => badWt (pop24 x)) (fun i => ims.getD i 0) 12 0

@[expose] def eighthPermOK (a : Array ℕ) : Bool :=
  amul (amul (amul a a) (amul a a)) (amul (amul a a) (amul a a)) == idArr &&
    eighthWeightBad a == 0

@[expose] def eighthCheck : Bool :=
  (List.range sylowCert.pts.size).all fun i => eighthPermOK sylowCert.pts[i]!

end CFSG.EvenSporadicStandard.TwoCo1
