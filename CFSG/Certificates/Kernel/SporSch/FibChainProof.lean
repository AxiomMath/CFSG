module

public import CFSG.Sporadic.Schreier.PairChain

public section

namespace CFSG.KS.SporSch.FibOrb

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open Finset

open scoped Classical in
theorem card_fib_countW {n : Nat} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hc : 0 < chunks) (h : rawChainOK n O S base W chunks = true) {groups : List (List ℕ)}
    (hg : groups.flatten = List.range Q.baseCount) {f : List (Array ℕ) → Bool}
    {Pr : Equiv.Perm (Fin n) → Prop}
    (hfP : ∀ w g, RepW n w g → g ∈ Q.originalSubgroup → (f w = true ↔ Pr g))
    {r0 r1 r2 : Nat} (word : Nat → Nat → Nat → List (Array ℕ)) (img : Nat → Nat)
    (hcount : ∀ F : List (Array ℕ) → Bool, countW F (blocksOf n (rawLevels n S base) groups) [] =
      ∑ k0 ∈ range r0, ∑ k1 ∈ range r1, ∑ k2 ∈ range r2,
        if F (word k0 k1 k2) = true then 1 else 0)
    (b : Fin n) (hev : ∀ k0 < r0, ∀ k1 < r1, ∀ k2 < r2, evR (word k0 k1 k2) b = img k0)
    {k0 : Nat} (hk0 : k0 < r0) (hinj : ∀ k < r0, img k = img k0 → k = k0) (a : Fin n)
    (ha : (a : Nat) = img k0) :
    Nat.card {x : Q.originalSubgroup // (x : Equiv.Perm (Fin n)) b = a ∧ Pr x} =
      ∑ k1 ∈ range r1, ∑ k2 ∈ range r2, if f (word k0 k1 k2) = true then 1 else 0 := by
  have key := card_eq_countW hA hc h hg (f := fun w => decide (evR w b = a) && f w)
    (Pr := fun g => g b = a ∧ Pr g) fun w g hw hgm => by
      rw [Bool.and_eq_true, decide_eq_true_iff, hfP w g hw hgm, hw b, Fin.val_inj]
  rw [key, hcount, Finset.sum_eq_single k0]
  · refine Finset.sum_congr rfl fun k1 hk1 => Finset.sum_congr rfl fun k2 hk2 => ?_
    rw [hev k0 hk0 k1 (mem_range.1 hk1) k2 (mem_range.1 hk2), ha]
    simp
  · intro k hk hne
    refine Finset.sum_eq_zero fun k1 hk1 => Finset.sum_eq_zero fun k2 hk2 => ?_
    have hk := mem_range.1 hk
    rw [hev k hk k1 (mem_range.1 hk1) k2 (mem_range.1 hk2), ha]
    have : img k ≠ img k0 := fun e => hne (hinj k hk e)
    simp [this]
  · intro hn
    exact absurd (mem_range.2 hk0) hn

end CFSG.KS.SporSch.FibOrb

end
