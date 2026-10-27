module

public import CFSG.GH74.Uniqueness.Section6Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

@[expose] def IsSTripleImage (Z : Set X) (M : Subgroup X) (γ δ ζ : Subgroup X) : Prop :=
  γ ∈ omega M ∧ δ ∈ omega M ∧ ζ ∈ omega M ∧ γ ≠ δ ∧ γ ≠ ζ ∧ δ ≠ ζ ∧
    ∃ s ∈ Z, conjugate γ s = γ ∧ conjugate δ s = ζ

@[expose] def Lemma61bStmt (Z : Set X) (M : Subgroup X) : Prop :=
  DoublyTransitive M → ∀ γ₁ δ₁ ζ₁ γ₂ δ₂ ζ₂ : Subgroup X, IsSTripleImage Z M γ₁ δ₁ ζ₁ →
    IsSTripleImage Z M γ₂ δ₂ ζ₂ →
      ∃ g : X, conjugate γ₁ g = γ₂ ∧ conjugate δ₁ g = δ₂ ∧ conjugate ζ₁ g = ζ₂

omit [Finite X] in
theorem lemma61b_of_lemma61a {Z : Set X} {M : Subgroup X} (h61a : Lemma61aStmt Z M) :
    Lemma61bStmt Z M := by
  rintro hD γ₁ δ₁ ζ₁ γ₂ δ₂ ζ₂ ⟨hγ₁, hδ₁, -, h1, -, -, s₁, hs₁, hs₁γ, hs₁δ⟩
    ⟨hγ₂, hδ₂, -, h2, -, -, s₂, hs₂, hs₂γ, hs₂δ⟩
  obtain ⟨g, hg1, hg2, hg3⟩ := h61a hD γ₁ δ₁ s₁ γ₂ δ₂ s₂ ⟨hγ₁, hδ₁, hs₁, hs₁γ, h1⟩
    ⟨hγ₂, hδ₂, hs₂, hs₂γ, h2⟩
  refine ⟨g, hg1, hg2, ?_⟩
  have e : g * (g⁻¹ * s₁ * g) = s₁ * g := by group
  rw [← hs₁δ, ← hs₂δ, ← hg2, ← hg3, conjugate_conjugate, conjugate_conjugate, e]

end CFSG.GH74.Uniqueness
