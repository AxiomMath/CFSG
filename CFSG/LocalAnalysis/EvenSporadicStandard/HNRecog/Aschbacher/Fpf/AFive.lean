module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Equiv Equiv.Perm

abbrev A5 : Type := alternatingGroup (Fin 5)

@[expose] def a₀ : A5 := ⟨finRotate 5, mem_alternatingGroup.2 (by decide)⟩

@[expose] def n₀ : A5 := ⟨swap 1 4 * swap 2 3, mem_alternatingGroup.2 (by decide)⟩

theorem orderOf_a₀ : orderOf a₀ = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [orderOf_eq_prime_iff]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem n₀_mul_a₀_mul_inv : n₀ * a₀ * n₀⁻¹ = a₀⁻¹ := by
  decide +kernel

theorem exists_conj_of_orderOf_eq_five {y : A5} (hy : orderOf y = 5) :
    ∃ z : A5, ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ y = z * a₀ ^ k * z⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hy5, hy1⟩ := orderOf_eq_prime_iff.mp hy
  have key : ∀ y : A5, y ^ 5 = 1 → y ≠ 1 →
      ∃ z : A5, y = z * a₀ * z⁻¹ ∨ y = z * a₀ ^ 2 * z⁻¹ := by
    decide +kernel
  obtain ⟨z, hz | hz⟩ := key y hy5 hy1
  · exact ⟨z, 1, Or.inl rfl, by simpa using hz⟩
  · exact ⟨z, 2, Or.inr rfl, by simpa using hz⟩

theorem exists_orderOf_eq_five_mul_conj {y : A5} (hy : y ≠ 1) :
    ∃ i j : ℕ, orderOf ((a₀ ^ i * y * (a₀ ^ i)⁻¹) * (a₀ ^ j * y * (a₀ ^ j)⁻¹)) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have key : ∀ y : A5, y ≠ 1 →
      ∃ i : Fin 5, ∃ j : Fin 5,
        ((a₀ ^ (i : ℕ) * y * (a₀ ^ (i : ℕ))⁻¹) *
          (a₀ ^ (j : ℕ) * y * (a₀ ^ (j : ℕ))⁻¹)) ^ 5 = 1 ∧
        ((a₀ ^ (i : ℕ) * y * (a₀ ^ (i : ℕ))⁻¹) *
          (a₀ ^ (j : ℕ) * y * (a₀ ^ (j : ℕ))⁻¹)) ≠ 1 := by
    decide +kernel
  obtain ⟨i, j, h5, h1⟩ := key y hy
  exact ⟨(i : ℕ), (j : ℕ), orderOf_eq_prime_iff.mpr ⟨h5, h1⟩⟩

theorem eq_top_of_fifteen_le_card {K : Subgroup A5} (hK : 15 ≤ Nat.card K) : K = ⊤ := by
  haveI : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  by_contra hne
  have hcard : Nat.card A5 = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide
  have h2 : K.index * Nat.card K = 60 := by rw [Subgroup.index_mul_card, hcard]
  have hidx : K.index ≤ 4 := by nlinarith [h2, hK]
  have hcore : K.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.mpr (h ▸ K.normalCore_le)) hne
  have hle : K.normalCore.index ≤ Nat.factorial K.index :=
    Subgroup.index_normalCore_le_factorial_index K
  rw [hcore, Subgroup.index_bot, hcard] at hle
  have hf : Nat.factorial K.index ≤ Nat.factorial 4 := Nat.factorial_le hidx
  have h4 : Nat.factorial 4 = 24 := by decide
  omega

end CFSG.EvenSporadicStandard.HNRecog.Fpf
