module

public import CFSG.ClassicalInvolution.Asc77.AscC25V2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Residual

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Mix25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R' a →
        (∃ r ∈ R, ∀ x ∈ R, (r⁻¹ * a) * x = x * (r⁻¹ * a)) ∨
          ∃ r ∈ R, (a * r) * (a * r) = 1 ∧ IsFAut R (a * r)

@[expose] def FF25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ∃ t' : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' ∧
          (∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), ⁅x, y⁆ ∈ lam R R' t') ∧
          ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → a⁻¹ * (g⁻¹ * a * g) ∈ lam R R' t'

end Residual


end CFSG.ClassicalInvolution.Asc77.C25V
