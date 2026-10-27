module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC18

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G]

structure Ctx18A (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) (𝒮 : Subgroup G) : Prop
    extends Ctx18 t L S x₁ x₂ lam rho tau om 𝒮 where
  card_C : Nat.card (ctxCY t tau x₁ x₂ rho) = 2 ^ 8

end CFSG.OddStandard.SmallF3.HarrisU33
