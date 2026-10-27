module

public import CFSG.ClassicalInvolution.Asc77.AscC25V34

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V
open scoped MatrixGroups commutatorElement

section Main

variable (p f : ℕ) [Fact p.Prime]


@[expose] def NStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R a → IsFAut R' a → z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
        ∀ t' : G, T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t' → (∃ g : G, g * z * g⁻¹ = t') →
          (¬ ∃ y : G, y * z * y⁻¹ = t' * z) → a * t' = t' * a →
            (¬ ∃ g : G, g * z * g⁻¹ = a * t') ∧ (¬ ∃ g : G, g * z * g⁻¹ = a * z * t')

end Main

end CFSG.ClassicalInvolution.Asc77.C25H
