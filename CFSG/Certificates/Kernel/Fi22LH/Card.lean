module

import CFSG.Certificates.Kernel.Fi22LH.OrbSets
import Mathlib.Data.Finset.Card
public import Certificates.Data.Kernel.Fi22.LHK

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native

theorem img_eq_of_sub {g e : Nat → Nat} (hg : ∀ i < 351, ∀ j < 351, g i = g j → i = j)
    (hsub : ∀ j < 351, ∃ j' < 351, e j' = g j) (y : Nat) :
    (∃ j' < 351, e j' = y) ↔ ∃ j < 351, g j = y := by
  classical
  let A := (Finset.range 351).image g
  let B := (Finset.range 351).image e
  have hA : A.card = 351 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    exact hg i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) e
  have hB : B.card ≤ 351 := Nat.le_trans Finset.card_image_le (by rw [Finset.card_range])
  have hAB : A ⊆ B := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j', hj', e'⟩ := hsub j (Finset.mem_range.1 hj)
    exact Finset.mem_image.2 ⟨j', Finset.mem_range.2 hj', e'⟩
  have hE : A = B := Finset.eq_of_subset_of_card_le hAB (by rw [hA]; exact hB)
  constructor
  · rintro ⟨j', hj', rfl⟩
    have : e j' ∈ A := by rw [hE]; exact Finset.mem_image.2 ⟨j', Finset.mem_range.2 hj', rfl⟩
    obtain ⟨j, hj, e'⟩ := Finset.mem_image.1 this
    exact ⟨j, Finset.mem_range.1 hj, e'⟩
  · rintro ⟨j, hj, rfl⟩
    exact hsub j hj

variable {Q : Nat → Nat} {al be : Nat}

theorem set_img_eq (hs : ∀ s < 20, setSl Q al be s = true) {m : Nat} (hm : m < 14080)
    {f : Nat → Nat} (hf : ∀ x < 3510, ∀ y < 3510, f x = f y → x = y) {q : Nat}
    (hq : ∀ i j, i < j → j < 351 → ent q i < ent q j) (hq' : ∀ j < 351, ent q j < 3510)
    (hsub : ∀ j < 351, (sb (Q m)).testBit (f (ent q j)) = true) (y : Nat) :
    (sb (Q m)).testBit y = true ↔ ∃ j < 351, f (ent q j) = y := by
  rw [sb_mem hs hm]
  refine img_eq_of_sub (fun i hi j hj e => ?_) (fun j hj => (sb_mem hs hm _).1 (hsub j hj)) y
  have := hf _ (hq' i hi) _ (hq' j hj) e
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · have := hq i j h1 hj
    omega
  · have := hq j i h1 hi
    omega

end CFSG.KS.Fi22LH
