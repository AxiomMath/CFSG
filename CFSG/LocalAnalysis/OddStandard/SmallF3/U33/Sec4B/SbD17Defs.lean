module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G]

@[expose] def ctxP (t tau x₁ x₂ rho : G) : Subgroup G :=
  ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)

@[expose] def ctxE0 (t tau x₁ x₂ rho om : G) : Subgroup G :=
  ctxP t tau x₁ x₂ rho ⊔ closure {tau, om}

variable [Finite G]

structure Ctx17 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) (𝒮 : Subgroup G) : Prop
    extends Ctx13 t L S x₁ x₂ lam rho tau om where
  sylow : IsSylowIn 2 𝒮 (ctxK t tau x₁ x₂ rho)
  U_le : ctxU t tau x₁ x₂ lam ≤ 𝒮
  Q_lt_P : ctxQ t tau x₁ x₂ rho < ctxP t tau x₁ x₂ rho

end CFSG.OddStandard.SmallF3.HarrisU33
