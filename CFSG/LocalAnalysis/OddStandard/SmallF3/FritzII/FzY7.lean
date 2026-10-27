module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzAssump

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

@[expose] def FzY7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → ¬ FzSylow T₂ →
    IsMulCommutative (fzP t x₁ x₂ rho) → 2 ^ 11 ∣ Nat.card G

@[expose] def FzY8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau : G), FzAssumptionII G → Ctx t L S x₁ x₂ lam rho tau →
    Nat.card (twoCore t) = 2 → IsFzT2 t x₁ x₂ S T₂ → ¬ FzSylow T₂ →
    ¬ IsMulCommutative (fzP t x₁ x₂ rho) → ¬ 2 ^ 11 ∣ Nat.card G → False

end CFSG.OddStandard.SmallF3.FritzII
