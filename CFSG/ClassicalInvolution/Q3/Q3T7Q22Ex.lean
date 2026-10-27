module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2201

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

@[expose] def ExactMembersHyp22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G),
    Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ → ExactMembers Ω

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
