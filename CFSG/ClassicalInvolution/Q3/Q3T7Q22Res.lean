module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q2201

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

@[expose] def OddCoreLayerNeg3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G),
    Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ (c t : G), c ≠ 1 → alphaOf (Subgroup.closure ({c, t} : Set G)) = ⊥ →
        Q3T8.Asc77.LayerOrthType Ω c 6 false → t ∈ ExactLayer.exactLayer Ω c → t * t = 1 →
        (¬ ∀ y ∈ ExactLayer.exactLayer Ω c, y * t = t * y) →
          classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c) = ⊥

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
