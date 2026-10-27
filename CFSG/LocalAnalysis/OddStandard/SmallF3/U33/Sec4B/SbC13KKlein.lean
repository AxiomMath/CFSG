module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G]

theorem c13K_mem_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {x : G} (hx : x ∈ closure ({a, b} : Set G)) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hba : b * a = a * b := hab.symm
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have hbab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have habA : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have habB : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have habab : a * b * (a * b) = 1 := by rw [mul_assoc, hbab, ha]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> simp
  | one => exact Or.inl rfl
  | mul y z _ _ hy hz =>
    rcases hy with rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl <;>
      simp [ha, hb, hba, haab, hbab, habA, habB, habab]
  | inv y _ hy =>
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    rcases hy with rfl | rfl | rfl | rfl
    · simp
    · simp [hai]
    · simp [hbi]
    · simp [mul_inv_rev, hai, hbi, hba]

theorem c13K_closure_pair_mem (a b : G) :
    (1 : G) ∈ closure ({a, b} : Set G) ∧ a ∈ closure ({a, b} : Set G) ∧
      b ∈ closure ({a, b} : Set G) ∧ a * b ∈ closure ({a, b} : Set G) :=
  ⟨one_mem _, subset_closure (by simp), subset_closure (by simp),
    mul_mem (subset_closure (by simp)) (subset_closure (by simp))⟩

theorem c13K_card_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card ↥(closure ({a, b} : Set G)) = 4 := by
  have hset : ((closure ({a, b} : Set G) : Subgroup G) : Set G) = {1, a, b, a * b} := by
    ext x
    constructor
    · intro hx
      have := c13K_mem_closure_pair ha hb hab hx
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    · intro hx
      obtain ⟨h1, h2, h3, h4⟩ := c13K_closure_pair_mem a b
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hab1 : a * b ≠ 1 := by
    intro h
    exact hne (by
      have : b = a⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← hab]
        exact h
      rw [this, hai])
  have haab : a ≠ a * b := by
    intro h
    exact hb1 (by simpa using h.symm)
  have hbab : b ≠ a * b := by
    intro h
    exact ha1 (by simpa using h.symm)
  have hcard : ({1, a, b, a * b} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hbab]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, haab⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
  calc Nat.card ↥(closure ({a, b} : Set G))
      = ((closure ({a, b} : Set G) : Subgroup G) : Set G).ncard :=
        (Nat.card_coe_set_eq _)
    _ = 4 := by rw [hset, hcard]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
