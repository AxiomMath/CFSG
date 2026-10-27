module

public import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.Enumerative.DoubleCounting

public section

namespace CFSG.KC.Misc.Lines

@[expose] def Ln (rb : Nat → Nat → Bool) (x y : Nat) : Finset Nat :=
  (Finset.range 693).filter fun z : Nat =>
    ∀ w : Nat, w < 693 → rb x w = true → rb y w = true → rb w z = true

theorem mem_Ln {rb : Nat → Nat → Bool} {x y z : Nat} :
    z ∈ Ln rb x y ↔ z < 693 ∧ ∀ w < 693, rb x w = true → rb y w = true → rb w z = true := by
  simp [Ln]

structure PolarRel (rb : Nat → Nat → Bool) : Prop where
  refl : ∀ x < 693, rb x x = true
  symm : ∀ x < 693, ∀ y < 693, rb x y = true → rb y x = true
  deg : ∀ p < 693, ((Finset.range 693).filter fun q : Nat => rb p q = true).card = 181
  card5 : ∀ x < 693, ∀ y < 693, x < y → rb x y = true → (Ln rb x y).card = 5

theorem Ln_comm (rb : Nat → Nat → Bool) (x y : Nat) : Ln rb x y = Ln rb y x := by
  ext z
  simp only [mem_Ln]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun w hw h1 h2 => h w hw h2 h1⟩
  · rintro ⟨hz, h⟩
    exact ⟨hz, fun w hw h1 h2 => h w hw h2 h1⟩

theorem lt_of_mem_Ln {rb : Nat → Nat → Bool} {x y z : Nat} (h : z ∈ Ln rb x y) : z < 693 :=
  (mem_Ln.1 h).1

namespace PolarRel

variable {rb : Nat → Nat → Bool} (H : PolarRel rb)
include H

theorem rb_symm {x y : Nat} (hx : x < 693) (hy : y < 693) : rb x y = rb y x := by
  cases h : rb x y
  · cases h' : rb y x
    · rfl
    · rw [H.symm y hy x hx h'] at h
      exact absurd h (by simp)
  · exact (H.symm x hx y hy h).symm

theorem card5' {x y : Nat} (hx : x < 693) (hy : y < 693) (hne : x ≠ y) (hxy : rb x y = true) :
    (Ln rb x y).card = 5 := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact H.card5 x hx y hy h hxy
  · rw [Ln_comm]
    exact H.card5 y hy x hx h (H.symm x hx y hy hxy)

theorem left_mem_Ln {x y : Nat} (hx : x < 693) : x ∈ Ln rb x y := by
  rw [mem_Ln]
  exact ⟨hx, fun w hw h1 _ => H.symm x hx w hw h1⟩

theorem right_mem_Ln {x y : Nat} (hy : y < 693) : y ∈ Ln rb x y := by
  rw [mem_Ln]
  exact ⟨hy, fun w hw _ h2 => H.symm y hy w hw h2⟩

theorem perp_left {x y z : Nat} (hx : x < 693) (hy : y < 693) (hxy : rb x y = true)
    (hz : z ∈ Ln rb x y) : rb x z = true :=
  (mem_Ln.1 hz).2 x hx (H.refl x hx) (H.symm x hx y hy hxy)

theorem perp_right {x y z : Nat} (hy : y < 693) (hxy : rb x y = true)
    (hz : z ∈ Ln rb x y) : rb y z = true :=
  (mem_Ln.1 hz).2 y hy hxy (H.refl y hy)

theorem perp_of_mem {x y p q : Nat} (hx : x < 693) (hy : y < 693) (hxy : rb x y = true)
    (hp : p ∈ Ln rb x y) (hq : q ∈ Ln rb x y) : rb p q = true := by
  have hq' := lt_of_mem_Ln hq
  have hp' := lt_of_mem_Ln hp
  have h := (mem_Ln.1 hp).2 q hq' (H.perp_left hx hy hxy hq) (H.perp_right hy hxy hq)
  exact H.symm q hq' p hp' h

theorem Ln_eq {x y p q : Nat} (hx : x < 693) (hy : y < 693) (hne : x ≠ y) (hxy : rb x y = true)
    (hpq : p ≠ q) (hp : p ∈ Ln rb x y) (hq : q ∈ Ln rb x y) : Ln rb p q = Ln rb x y := by
  have hp' := lt_of_mem_Ln hp
  have hq' := lt_of_mem_Ln hq
  have hpq' : rb p q = true := H.perp_of_mem hx hy hxy hp hq
  refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
  · rw [mem_Ln] at hz ⊢
    refine ⟨hz.1, fun w hw h1 h2 => ?_⟩
    have a1 := (mem_Ln.1 hp).2 w hw h1 h2
    have a2 := (mem_Ln.1 hq).2 w hw h1 h2
    exact hz.2 w hw (H.symm w hw p hp' a1) (H.symm w hw q hq' a2)
  · rw [H.card5' hx hy hne hxy, H.card5' hp' hq' hpq hpq']

theorem lines_count (n : Nat) (LS : Nat → Finset Nat)
    (ha : ∀ i < n, ∃ x < 693, ∃ y < 693, x ≠ y ∧ rb x y = true ∧ LS i = Ln rb x y)
    (hb : ∀ i < n, ∀ j < n, LS i = LS j → i = j)
    (hc : ∀ x < 693, ∀ y < 693, x ≠ y → rb x y = true → ∃ i < n, LS i = Ln rb x y) :
    (∀ p < 693, ((Finset.range n).filter fun i : Nat => p ∈ LS i).card = 45) ∧ n = 6237 := by
  have key : ∀ p < 693, ((Finset.range n).filter fun i : Nat => p ∈ LS i).card = 45 := by
    intro p hp
    have hQ : ((Finset.range 693).filter fun q : Nat => q ≠ p ∧ rb p q = true).card = 180 := by
      have e : ((Finset.range 693).filter fun q : Nat => q ≠ p ∧ rb p q = true) =
          ((Finset.range 693).filter fun q : Nat => rb p q = true).erase p := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
        tauto
      have hmem : p ∈ ((Finset.range 693).filter fun q : Nat => rb p q = true) := by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hp, H.refl p hp⟩
      rw [e, Finset.card_erase_of_mem hmem, H.deg p hp]
    have hm : ∀ i ∈ ((Finset.range n).filter fun i : Nat => p ∈ LS i),
        (((Finset.range 693).filter fun q : Nat => q ≠ p ∧ rb p q = true).bipartiteAbove
          (fun i q => q ∈ LS i) i).card = 4 := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hin, hpi⟩ := hi
      obtain ⟨x, hx, y, hy, hne, hxy, hLS⟩ := ha i hin
      have e : ((Finset.range 693).filter fun q : Nat => q ≠ p ∧ rb p q = true).bipartiteAbove
          (fun i q => q ∈ LS i) i = (LS i).erase p := by
        ext q
        simp only [Finset.mem_bipartiteAbove, Finset.mem_filter, Finset.mem_range,
          Finset.mem_erase]
        constructor
        · rintro ⟨⟨-, hqp, -⟩, hq⟩
          exact ⟨hqp, hq⟩
        · rintro ⟨hqp, hq⟩
          rw [hLS] at hq hpi
          exact ⟨⟨lt_of_mem_Ln hq, hqp, H.perp_of_mem hx hy hxy hpi hq⟩, by rw [hLS]; exact hq⟩
      rw [e, Finset.card_erase_of_mem hpi, hLS, H.card5' hx hy hne hxy]
    have hn : ∀ q ∈ ((Finset.range 693).filter fun q : Nat => q ≠ p ∧ rb p q = true),
        (((Finset.range n).filter fun i : Nat => p ∈ LS i).bipartiteBelow
          (fun i q => q ∈ LS i) q).card = 1 := by
      intro q hq
      rw [Finset.mem_filter, Finset.mem_range] at hq
      obtain ⟨hq693, hqp, hpq⟩ := hq
      rw [Finset.card_eq_one]
      obtain ⟨i0, hi0, hLS0⟩ := hc p hp q hq693 (Ne.symm hqp) hpq
      refine ⟨i0, ?_⟩
      ext i
      simp only [Finset.mem_bipartiteBelow, Finset.mem_filter, Finset.mem_range,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hin, hpi⟩, hqi⟩
        obtain ⟨x, hx, y, hy, hne, hxy, hLS⟩ := ha i hin
        have hLSi : LS i = Ln rb p q := by
          rw [hLS] at hpi hqi ⊢
          exact (H.Ln_eq hx hy hne hxy (Ne.symm hqp) hpi hqi).symm
        exact hb i hin i0 hi0 (hLSi.trans hLS0.symm)
      · rintro rfl
        refine ⟨⟨hi0, ?_⟩, ?_⟩
        · rw [hLS0]; exact H.left_mem_Ln hp
        · rw [hLS0]; exact H.right_mem_Ln hq693
    have := Finset.card_mul_eq_card_mul (fun i q => q ∈ LS i) hm hn
    omega
  refine ⟨key, ?_⟩
  have hm : ∀ p ∈ Finset.range 693,
      ((Finset.range n).bipartiteAbove (fun p i => p ∈ LS i) p).card = 45 := by
    intro p hp
    rw [Finset.mem_range] at hp
    exact key p hp
  have hn : ∀ i ∈ Finset.range n,
      ((Finset.range 693).bipartiteBelow (fun p i => p ∈ LS i) i).card = 5 := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨x, hx, y, hy, hne, hxy, hLS⟩ := ha i hi
    have e : (Finset.range 693).bipartiteBelow (fun p i => p ∈ LS i) i = LS i := by
      ext p
      simp only [Finset.mem_bipartiteBelow, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        rw [hLS] at h
        exact ⟨lt_of_mem_Ln h, by rw [hLS]; exact h⟩
    rw [e, hLS, H.card5' hx hy hne hxy]
  have := Finset.card_mul_eq_card_mul (fun p i => p ∈ LS i) hm hn
  simp only [Finset.card_range] at this
  omega

end PolarRel

end CFSG.KC.Misc.Lines

end
