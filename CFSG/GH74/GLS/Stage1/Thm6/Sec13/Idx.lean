module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem card_le_two_mul_inf [Finite G] {K H₀ : Subgroup G}
    (hprod : ∀ a ∈ K, ∀ b ∈ K, a ∉ H₀ → b ∉ H₀ → a * b ∈ H₀) :
    Nat.card K ≤ 2 * Nat.card ↥(K ⊓ H₀) := by
  have hdvd : (K ⊓ H₀).relIndex K ∣ 2 := by
    rw [relIndex_dvd_two_iff]
    by_cases hK : K ≤ H₀
    · refine ⟨1, K.one_mem, fun b hb => Or.inr ⟨hb, hK hb⟩⟩
    · rw [IsConcreteLE.le_iff] at hK
      push Not at hK
      obtain ⟨a, haK, haH⟩ := hK
      refine ⟨a, haK, fun b hb => ?_⟩
      by_cases hbH : b ∈ H₀
      · exact Or.inr ⟨hb, hbH⟩
      · exact Or.inl ⟨K.mul_mem hb haK, hprod b hb a haK hbH haH⟩
  have h2 : (K ⊓ H₀).relIndex K ≤ 2 := Nat.le_of_dvd Nat.two_pos hdvd
  have := relIndex_mul_card (K ⊓ H₀) K
  rw [inf_eq_left.2 (inf_le_left : K ⊓ H₀ ≤ K)] at this
  calc Nat.card K = (K ⊓ H₀).relIndex K * Nat.card ↥(K ⊓ H₀) := this.symm
    _ ≤ 2 * Nat.card ↥(K ⊓ H₀) := Nat.mul_le_mul_right _ h2

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
