module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFInputs

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding

@[expose] def NoFFModule (Y : Type) [Group Y] : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H L : Subgroup (MulAut V), FFHyp H L →
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* Y) → ¬ IsFFModule H

end CFSG.HardMathSupport.Cooperstein.Coordinator
