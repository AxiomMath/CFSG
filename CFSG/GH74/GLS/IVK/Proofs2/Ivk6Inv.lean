module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup

section Enum

theorem eq_of_card_four {G : Type*} [Group G] {U : Subgroup G} (hU : Nat.card ↥U = 4)
    {a b c d : G} (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hd : d ∈ U) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {t : G} (ht : t ∈ U) :
    t = a ∨ t = b ∨ t = c ∨ t = d := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hta, htb, htc, htd⟩ := hcon
  have hta' : a ≠ t := fun h => hta h.symm
  have htb' : b ≠ t := fun h => htb h.symm
  have htc' : c ≠ t := fun h => htc h.symm
  have htd' : d ≠ t := fun h => htd h.symm
  have hfin : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hU]; norm_num)
  have : Fintype ↥U := Fintype.ofFinite ↥U
  have h4 : ((U : Set G).toFinset).card = 4 := by
    rw [← hU, Nat.card_eq_fintype_card]
    exact Set.toFinset_card (U : Set G)
  have hsub : ({a, b, c, d, t} : Finset G) ⊆ (U : Set G).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simpa
  have h5 : ({a, b, c, d, t} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [htd']
    · simp [hcd, htc']
    · simp [hbc, hbd, htb']
    · simp [hab, hac, had, hta']
  have := Finset.card_le_card hsub
  omega

end Enum

section Swap

variable {G : Type*} [Group G]

theorem exists_involution_of_normalizing {U : Subgroup G} (hU4 : Nat.card ↥U = 4)
    (hUsq : ∀ a ∈ U, a ^ 2 = 1) {w : G} (hwN : w ∈ normalizer (U : Set G)) (hw2U : w ^ 2 ∈ U)
    (hwc : ¬ ∀ u ∈ U, u * w = w * u) (hwU : w ∉ U) :
    ∃ z ∈ U, ∃ x ∈ U, z ≠ 1 ∧ x * w ∉ U ∧ (x * w) ^ 2 = 1 ∧ z * (x * w) = (x * w) * z := by
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => by
    have h1 : a * a = 1 := by rw [← pow_two]; exact hUsq a ha
    have h2 : b * b = 1 := by rw [← pow_two]; exact hUsq b hb
    have h3 : (a * b) * (a * b) = 1 := by rw [← pow_two]; exact hUsq _ (U.mul_mem ha hb)
    have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right h1
    have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right h2
    have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h3
    calc a * b = (a * b)⁻¹ := e3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [e1, e2]
  have hw2U' : w * w ∈ U := by rw [← pow_two]; exact hw2U
  have hUinv : ∀ a ∈ U, a⁻¹ = a := fun a ha => by
    have h1 : a * a = 1 := by rw [← pow_two]; exact hUsq a ha
    exact inv_eq_of_mul_eq_one_right h1
  have hmv : ∃ x ∈ U, w * x ≠ x * w := by
    by_contra hcon
    apply hwc
    intro u hu
    by_contra hne
    exact hcon ⟨u, hu, fun h => hne h.symm⟩
  obtain ⟨x, hx, hwx⟩ := hmv
  set y : G := w * x * w⁻¹ with hy
  have hyU : y ∈ U := (Subgroup.mem_normalizer_iff.1 hwN x).1 hx
  have hyx : y ≠ x := by
    intro h
    apply hwx
    have : w * x * w⁻¹ * w = x * w := by rw [← hy, h]
    simpa [mul_assoc] using this
  have hx1 : x ≠ 1 := by
    intro h
    apply hwx
    rw [h, mul_one, one_mul]
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    have : w * x * w⁻¹ = 1 := by rw [← hy]; exact h
    have h2 : x = w⁻¹ * (w * x * w⁻¹) * w := by group
    rw [h2, this]
    group
  set z : G := x * y with hz
  have hzU : z ∈ U := U.mul_mem hx hyU
  have hzx : z ≠ x := by
    intro h
    apply hy1
    have : x * y = x * 1 := by rw [← hz, h, mul_one]
    exact mul_left_cancel this
  have hzy : z ≠ y := by
    intro h
    apply hx1
    have : x * y = 1 * y := by rw [← hz, h, one_mul]
    exact mul_right_cancel this
  have hz1 : z ≠ 1 := by
    intro h
    apply hyx
    have h1 : x * y = 1 := by rw [← hz]; exact h
    have : y = x⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, hUinv x hx]
  have hx1' : (1 : G) ≠ x := fun h => hx1 h.symm
  have hy1' : (1 : G) ≠ y := fun h => hy1 h.symm
  have hz1' : (1 : G) ≠ z := fun h => hz1 h.symm
  have hxy' : x ≠ y := fun h => hyx h.symm
  have hxz' : x ≠ z := fun h => hzx h.symm
  have hyz' : y ≠ z := fun h => hzy h.symm
  have hwyx : w * y * w⁻¹ = x := by
    have hc : x * (w * w) = (w * w) * x := hUc x hx _ hw2U'
    calc w * y * w⁻¹ = w * (w * x * w⁻¹) * w⁻¹ := by rw [hy]
      _ = (w * w) * x * (w * w)⁻¹ := by group
      _ = x := by rw [← hc]; group
  have hwz : w * z = z * w := by
    have h1 : w * z * w⁻¹ = z := by
      calc w * z * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) := by rw [hz]; group
        _ = y * x := by rw [← hy, hwyx]
        _ = x * y := hUc y hyU x hx
        _ = z := hz.symm
    calc w * z = (w * z * w⁻¹) * w := by group
      _ = z * w := by rw [h1]
  have hw2c : w * (w * w) = (w * w) * w := by group
  have ht : w * w = 1 ∨ w * w = z := by
    rcases eq_of_card_four hU4 (U.one_mem) hx hyU hzU hx1' hy1' hz1' hxy' hxz' hyz' hw2U' with
      h | h | h | h
    · exact Or.inl h
    · exfalso
      apply hwx
      rw [h] at hw2c
      exact hw2c
    · exfalso
      rw [h] at hw2c
      apply hyx
      have : w * y * w⁻¹ = y := by
        calc w * y * w⁻¹ = (w * y) * w⁻¹ := rfl
          _ = (y * w) * w⁻¹ := by rw [hw2c]
          _ = y := by group
      rw [← this, hwyx]
    · exact Or.inr h
  rcases ht with ht | ht
  · refine ⟨z, hzU, 1, U.one_mem, hz1, ?_, ?_, ?_⟩
    · simpa using hwU
    · rw [pow_two]
      simpa using ht
    · simpa using hwz.symm
  · refine ⟨z, hzU, x, hx, hz1, ?_, ?_, ?_⟩
    · intro h
      apply hwU
      have : x⁻¹ * (x * w) ∈ U := U.mul_mem (U.inv_mem hx) h
      simpa using this
    · have hwxw : w⁻¹ * x * w = y := by
        have h1 : w * y * w⁻¹ = x := hwyx
        have h2 : y = w⁻¹ * x * w := by
          calc y = w⁻¹ * (w * y * w⁻¹) * w := by group
            _ = w⁻¹ * x * w := by rw [h1]
        exact h2.symm
      calc (x * w) ^ 2 = x * (w * x * w⁻¹) * (w * w) := by rw [pow_two]; group
        _ = x * y * z := by rw [← hy, ht]
        _ = z * z := by rw [← hz]
        _ = 1 := by rw [← pow_two]; exact hUsq z hzU
    · calc z * (x * w) = x * (z * w) := by
            have := hUc z hzU x hx
            calc z * (x * w) = (z * x) * w := by group
              _ = (x * z) * w := by rw [this]
              _ = x * (z * w) := by group
        _ = x * (w * z) := by rw [hwz]
        _ = (x * w) * z := by group

end Swap

end CFSG.GH74.GLS.IVK.Proofs2
