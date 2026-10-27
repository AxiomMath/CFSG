module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M1
public import CFSG.ClassicalInvolution.Q3.Q3T7F25M6

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Hat2A7M
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

@[expose] def C25_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ A : Subgroup G, z ∈ A → A ≤ (S : Subgroup G) →
      (∀ s ∈ (S : Subgroup G), conjSub s A = A) →
      (∀ a ∈ A, a ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))) → A = Subgroup.zpowers z
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7T
open CFSG.ClassicalInvolution.Asc77.T7T
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem c25_5_proved : C25_5 := by
    intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
    exact CFSG.ClassicalInvolution.T7F25.Asc77.T7T.c25_5_proved G Ω K K' W S R R' z t u₁ u₂ hyp.toF
end T7T
end Asc77
end
end CFSG.ClassicalInvolution.Hat2A7M
