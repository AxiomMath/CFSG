module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzAssump
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Ctx

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

@[expose] def FzCaseIIr2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S : Subgroup G)
    (x₁ x₂ lam rho tau : G), ¬ 2 ^ 11 ∣ Nat.card G → FzAssumptionII G →
    Ctx t L S x₁ x₂ lam rho tau → Nat.card (twoCore t) = 4 → False

end CFSG.OddStandard.SmallF3.FritzII
