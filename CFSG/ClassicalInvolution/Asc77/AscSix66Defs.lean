module

public import CFSG.ClassicalInvolution.Asc77.WP1Section6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

section Cyc

variable {G : Type} [Group G]

@[expose] def Cyc66 (Ω : Set (Subgroup G)) : Prop :=
  ∀ S : Subgroup G, IsPGroup 2 S → ∀ Δ : Set (Subgroup G), (∀ A ∈ Δ, A ≤ S) →
    (∀ A ∈ Δ, ∀ s ∈ S, conjSub s A ∈ Δ) →
      (∀ A ∈ Δ, IsCyclic ↥A ∧ 4 ≤ Nat.card ↥A) →
        (∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ∃ J ∈ Ω, ∃ J' ∈ Ω, J ≠ J' ∧ A ≤ J ∧ B ≤ J') →
          ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B

end Cyc

variable (p f : ℕ) [Fact p.Prime]

@[expose] def L6_6i : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      ∀ S : Subgroup G, IsPGroup 2 S → ∀ Δ : Set (Subgroup G), (∀ A ∈ Δ, A ≤ S) →
        (∀ A ∈ Δ, ∀ s ∈ S, conjSub s A ∈ Δ) → Δ ⊆ RSet Ω →
          ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B

@[expose] def L6_6ii : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω → Cyc66 Ω

@[expose] def L6_6iiAEmpty : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod p f Ω →
      (∀ K ∈ Ω, AEmpty Ω K) → Cyc66 Ω

theorem l6_6_of_i_ii (hi : L6_6i p f) (hii : L6_6ii p f) : L6_6 p f := by
  intro hp hq G _ _ Ω hΩ S hS Δ hΔS hΔinv hcase A hA B hB hne
  rcases hcase with h | ⟨hc, hd⟩
  · exact hi hp hq G Ω hΩ S hS Δ hΔS hΔinv h A hA B hB hne
  · exact hii hp hq G Ω hΩ S hS Δ hΔS hΔinv hc hd A hA B hB hne

theorem l6_6i_of_l6_6 (h : L6_6 p f) : L6_6i p f := by
  intro hp hq G _ _ Ω hΩ S hS Δ hΔS hΔinv hR A hA B hB hne
  exact h hp hq G Ω hΩ S hS Δ hΔS hΔinv (Or.inl hR) A hA B hB hne

theorem l6_6ii_of_l6_6 (h : L6_6 p f) : L6_6ii p f := by
  intro hp hq G _ _ Ω hΩ S hS Δ hΔS hΔinv hc hd A hA B hB hne
  exact h hp hq G Ω hΩ S hS Δ hΔS hΔinv (Or.inr ⟨hc, hd⟩) A hA B hB hne

theorem l6_6iiAEmpty_of_l6_6ii (h : L6_6ii p f) : L6_6iiAEmpty p f :=
  fun hp hq G _ _ Ω hΩ _ => h hp hq G Ω hΩ

end CFSG.ClassicalInvolution.Asc77
