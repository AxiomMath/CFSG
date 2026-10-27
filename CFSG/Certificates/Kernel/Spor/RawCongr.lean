module

public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.KS.Raw

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem allLt_congr {n : Nat} {p q : Nat → Bool} (h : ∀ i < n, p i = q i) :
    allLt n p = allLt n q := by
  unfold allLt
  rw [Bool.eq_iff_iff, Nat.all_eq_finRange_all, Nat.all_eq_finRange_all, List.all_eq_true,
    List.all_eq_true]
  constructor
  · intro hp ⟨i, hi⟩ hm
    have := hp ⟨i, hi⟩ hm
    simpa [h i hi] using this
  · intro hq ⟨i, hi⟩ hm
    have := hq ⟨i, hi⟩ hm
    simpa [h i hi] using this

theorem rawChainOK_congr {n : Nat} {O O' S : Array (Array Nat)} {base : Array Nat}
    {W : Array (List Int)} {chunks : Nat} (hs : O.size = O'.size)
    (he : ∀ k < O.size, eqA n S[k]! O[k]! = eqA n S[k]! O'[k]!) :
    rawChainOK n O S base W chunks = rawChainOK n O' S base W chunks := by
  unfold rawChainOK
  rw [allLt_congr he, hs]

end CFSG.KS.Raw

end
