module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type*} [Group G]

private lemma pair_mul {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ x ∈ ({g : G | g = 1 ∨ g = a ∨ g = b ∨ g = a * b} : Set G),
      ∀ y ∈ ({g : G | g = 1 ∨ g = a ∨ g = b ∨ g = a * b} : Set G),
      x * y ∈ ({g : G | g = 1 ∨ g = a ∨ g = b ∨ g = a * b} : Set G) := by
  have hba : b * a = a * b := hab.symm
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : (a * b) * a = b := by rw [mul_assoc, ← hab, h1]
  have h3 : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
  have h4 : b * (a * b) = a := by rw [← mul_assoc, hba, h3]
  have h5 : (a * b) * (a * b) = 1 := by rw [← mul_assoc, h2, hb]
  intro x hx y hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp only [Set.mem_setOf_eq, one_mul, mul_one, ha, hb, h1, h2, h3, h4, h5, hba,
      eq_self_iff_true, or_true, true_or, or_false, false_or]

private lemma pair_inv {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ x ∈ ({g : G | g = 1 ∨ g = a ∨ g = b ∨ g = a * b} : Set G),
      x⁻¹ ∈ ({g : G | g = 1 ∨ g = a ∨ g = b ∨ g = a * b} : Set G) := by
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : (a * b) * a = b := by rw [mul_assoc, ← hab, h1]
  have h5 : (a * b) * (a * b) = 1 := by rw [← mul_assoc, h2, hb]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp only [Set.mem_setOf_eq, inv_one, inv_eq_of_mul_eq_one_right ha,
      inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right h5,
      eq_self_iff_true, or_true, true_or, or_false, false_or]

theorem mem_closure_pair_cases {a b : G} (hab : a * b = b * a) (ha : a * a = 1) (hb : b * b = 1)
    {x : G} (hx : x ∈ closure {a, b}) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  let E : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = a ∨ g = b ∨ g = a * b}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        exact pair_mul ha hb hab x hx y hy
      inv_mem' := by
        intro x hx
        exact pair_inv ha hb hab x hx }
  have hEsub : ({a, b} : Set G) ⊆ E := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  exact (Subgroup.closure_le (K := E)).mpr hEsub hx

theorem isPGroup_closure_pair {a b : G} (hab : a * b = b * a) (ha : a * a = 1) (hb : b * b = 1) :
    IsPGroup 2 (closure {a, b} : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro x
  have hx : (x : G) = 1 ∨ (x : G) = a ∨ (x : G) = b ∨ (x : G) = a * b :=
    mem_closure_pair_cases hab ha hb x.2
  rw [← Subgroup.orderOf_coe x]
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : (a * b) * a = b := by rw [mul_assoc, ← hab, h1]
  have h5 : (a * b) * (a * b) = 1 := by rw [← mul_assoc, h2, hb]
  have hsq : (x : G) ^ 2 = 1 := by
    rcases hx with h | h | h | h <;> rw [h]
    · simp
    · simpa [pow_two] using ha
    · simpa [pow_two] using hb
    · simpa [pow_two] using h5
  have hdvd : orderOf (x : G) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
