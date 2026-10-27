module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem eq_or_eq_or_eq_or_eq_of_ncard_le_four {α : Type*} {S : Set α} (hS : S.Finite)
    (hcard : S.ncard ≤ 4) {a b c d : α} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {y : α} (hy : y ∈ S) : y = a ∨ y = b ∨ y = c ∨ y = d := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h1, h2, h3, h4⟩ := hne
  have hsub : ({y, a, b, c, d} : Set α) ⊆ S := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
  have e1 : ({c, d} : Set α).ncard = 2 := Set.ncard_pair hcd
  have e2 : ({b, c, d} : Set α).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hbc, hbd]), e1]
  have e3 : ({a, b, c, d} : Set α).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac, had]), e2]
  have e4 : ({y, a, b, c, d} : Set α).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3, h4]), e3]
  have := Set.ncard_le_ncard hsub hS
  omega

theorem ne_of_sq_eq_one {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) :
    (1 : G) ≠ a ∧ (1 : G) ≠ b ∧ (1 : G) ≠ a * b ∧ a ≠ b ∧ a ≠ a * b ∧ b ≠ a * b := by
  refine ⟨ha1.symm, hb1.symm, ?_, hab, ?_, ?_⟩
  · intro h
    apply hab
    have h2 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    have h3 : a⁻¹ = a := by
      rw [inv_eq_iff_mul_eq_one, ← sq]
      exact ha
    rw [h2, h3]
  · intro h
    apply hb1
    have : a * 1 = a * b := by
      rw [mul_one]
      exact h
    exact (mul_left_cancel this).symm
  · intro h
    apply ha1
    have : 1 * b = a * b := by
      rw [one_mul]
      exact h
    exact (mul_right_cancel this).symm

theorem mul_conj_comm_of_conj_mem {G : Type*} [Group G] {P Q : Set G} {t c : G}
    (ht : ∀ p ∈ P, p * t = t * p) (hc : ∀ r ∈ Q, c⁻¹ * r * c ∈ P) {r : G} (hr : r ∈ Q) :
    r * (c * t * c⁻¹) = c * t * c⁻¹ * r := by
  have h := ht _ (hc r hr)
  calc r * (c * t * c⁻¹) = c * ((c⁻¹ * r * c) * t) * c⁻¹ := by group
    _ = c * (t * (c⁻¹ * r * c)) * c⁻¹ := by rw [h]
    _ = c * t * c⁻¹ * r := by group

theorem smul_eq_self_of_mem_orbit_of_forall_mul_comm {G X : Type*} [Group G] [MulAction G X]
    {Q : Subgroup G} {z : G} (hz : ∀ r ∈ Q, r * z = z * r) {x : X} (hzx : z • x = x) {y : X}
    (hy : y ∈ MulAction.orbit ↥Q x) : z • y = y := by
  obtain ⟨⟨r, hr⟩, rfl⟩ := hy
  change z • ((r : G) • x) = (r : G) • x
  rw [← mul_smul, ← hz r hr, mul_smul, hzx]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
