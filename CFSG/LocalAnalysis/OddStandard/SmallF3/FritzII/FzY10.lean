module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzShape
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzAssump
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

@[expose] def FzY10Shape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → FzSylow T₂ →
    ∃ a₁₂ a₂₂ a₃₂ : G, FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂

end CFSG.OddStandard.SmallF3.FritzII
