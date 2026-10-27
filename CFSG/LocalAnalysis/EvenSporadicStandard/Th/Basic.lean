module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup
open scoped commutatorElement

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {H : Type*} [Group H] {y x : H}
    (hy : orderOf y = 2) (hx : x ∈ zpowers y) : x = 1 ∨ x = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hy, Nat.cast_ofNat]
  have : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases this with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem eq_of_orderOf_eq_two_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H] {u v : H}
    (hu : orderOf u = 2) (hv : orderOf v = 2) : u = v := by
  have heq : zpowers u = zpowers v := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hu, hv]
  have hmem : v ∈ zpowers u := heq ▸ mem_zpowers v
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hu hmem with h | h
  · rw [h, orderOf_one] at hv
    omega
  · exact h.symm

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hAB : B ≤ centralizer (A : Set G)) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (hAB hb) a ha
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        rw [mul_assoc, ← mul_assoc b, ← hcomm a' ha' b hb]
        group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [mul_one]⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by rw [mul_one]⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul]⟩)
  exact hle hx

theorem commutator_mul_mul_of_commute {l l' r r' : G} (h2 : Commute r l') (h3 : Commute r' l)
    (h5 : Commute r r') : ⁅l * r, l' * r'⁆ = ⁅l, l'⁆ := by
  simp only [commutatorElement_def]
  calc l * r * (l' * r') * (l * r)⁻¹ * (l' * r')⁻¹
      = l * (r * l') * (r' * r⁻¹) * l⁻¹ * r'⁻¹ * l'⁻¹ := by group
    _ = l * (l' * r) * (r⁻¹ * r') * l⁻¹ * r'⁻¹ * l'⁻¹ := by
        rw [h2.eq, (h5.inv_left).eq.symm]
    _ = l * l' * (r * r⁻¹) * r' * l⁻¹ * r'⁻¹ * l'⁻¹ := by group
    _ = l * l' * r' * l⁻¹ * r'⁻¹ * l'⁻¹ := by group
    _ = l * l' * (r' * l⁻¹) * r'⁻¹ * l'⁻¹ := by group
    _ = l * l' * (l⁻¹ * r') * r'⁻¹ * l'⁻¹ := by rw [h3.inv_right.eq]
    _ = l * l' * l⁻¹ * l'⁻¹ := by group

theorem commutator_sup_le_left {L R : Subgroup G} (hLR : R ≤ centralizer (L : Set G))
    (hR : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r) : ⁅L ⊔ R, L ⊔ R⁆ ≤ L := by
  have hcomm : ∀ l ∈ L, ∀ r ∈ R, l * r = r * l := fun l hl r hr =>
    mem_centralizer_iff.1 (hLR hr) l hl
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨l, hl, r, hr, rfl⟩ := exists_mul_of_mem_sup hLR hx
  obtain ⟨l', hl', r', hr', rfl⟩ := exists_mul_of_mem_sup hLR hy
  rw [commutator_mul_mul_of_commute (Commute.symm (hcomm l' hl' r hr))
    (Commute.symm (hcomm l hl r' hr')) (hR r hr r' hr')]
  simp only [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem hl hl') (L.inv_mem hl)) (L.inv_mem hl')

end CFSG.EvenSporadicStandard.ThStd
