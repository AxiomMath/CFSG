module

public import CFSG.Goldschmidt.Steps.G2Fin
public import CFSG.Goldschmidt.Steps.G2Grp

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.QuasithinUnique G2
open scoped Pointwise

theorem G211T :
    ∀ (G : Type) [Group G] [Finite G] (A X : Subgroup G) (y : G), ONanHyp A X y →
      (∀ X₀ : Subgroup G, X₀ ≤ X → X ⊓ Subgroup.centralizer (A : Set G) ≤ X₀ →
        (X₀.subgroupOf X).index ≠ 2) →
      (∀ x ∈ X, conjSub x (A ⊓ Subgroup.centralizer ({y} : Set G)) =
          A ⊓ Subgroup.centralizer ({y} : Set G) →
        x⁻¹ * y * x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A : Set G)) →
      (∀ b ∈ A, ∀ c ∈ A, b ≠ 1 → c ≠ 1 → ∃ x ∈ X, x⁻¹ * b * x = c) →
      Nat.card A = 8 ∧ Nat.card (A ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) = 2 ∧
        ((X ⊓ Subgroup.centralizer (A : Set G)).subgroupOf X).index = 21 ∧
        ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∉ Subgroup.centralizer (A : Set G) := by
  intro G _ _ A X y h hI hN hT
  have : Fact (IsElemAbelian 2 A) := ⟨h.elem⟩
  have hL := linHyp_of_onanHyp h
  have hfix : fixSp (conjRep h.le ⟨y, h.mem⟩) = sub A (Subgroup.centralizer ({y} : Set G)) :=
    fixSp_conjRep h.le ⟨y, h.mem⟩
  obtain ⟨h8, h2, h21, x₁, hx₁, x₂, hx₂, hne⟩ := hL.eq_of_transitive
    (index_ne_two_of_onanHyp h hI) (normalizes_of_onanHyp h hN)
    ((transitive_iff_of_onanHyp h).mp hT)
  refine ⟨?_, ?_, ?_, exists_commutator_of_onanHyp h hx₁ hx₂ hne⟩
  · rw [← card_additive]
    exact h8
  · rw [← card_sub, ← hfix]
    exact h2
  · rw [index_eq_card_of_onanHyp h]
    exact h21

end CFSG.Goldschmidt
