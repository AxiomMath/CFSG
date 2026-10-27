module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzShape

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G]

@[expose] def fzR6 (t x₁ x₂ a₁₂ a₂₂ a₃₂ : G) : Subgroup G :=
  closure {x₁ * t, a₁₂, x₂ * t, a₂₂, (x₁ * x₂)⁻¹ * t, a₃₂}

structure FzSetting7 [Finite G] (t : G) (L S T₂ : Subgroup G)
    (x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ : G) : Prop where
  ctx : Ctx t L S x₁ x₂ lam rho tau
  card_twoCore : Nat.card (twoCore t) = 2
  isT2 : IsFzT2 t x₁ x₂ S T₂
  sylow : FzSylow T₂
  shape : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂

end CFSG.OddStandard.SmallF3.FritzII
