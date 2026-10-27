module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzAssump

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

@[expose] def FzCaseI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S : Subgroup G)
    (x₁ x₂ lam rho : G), FzAssumptionII G → Ctx0 t L S x₁ x₂ lam rho →
    invCent t = twoCore t ⊔ L → False

end CFSG.OddStandard.SmallF3.FritzII
