module

public import CFSG.ClassicalInvolution.Q3.Q3T8L274A

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Defs

@[expose] def LayerShapeAt {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K J' : Subgroup G) (c : G) : Prop :=
  ¬ T3.DStarConnected (Q3T7.layerFam3 Ω c) ∨
    ∀ M ∈ Q3T7.layerFam3 Ω c,
      M = Layer.layerImg3 Ω c K ∨ M = Layer.layerImg3 Ω c J'

end Defs

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
