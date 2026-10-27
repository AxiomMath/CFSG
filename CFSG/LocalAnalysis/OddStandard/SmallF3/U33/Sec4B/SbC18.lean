module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbD17Defs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G]

@[expose] def ctxOK (t tau x₁ x₂ rho : G) : Subgroup G :=
  CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho)

@[expose] def ctxCY (t tau x₁ x₂ rho : G) : Subgroup G :=
  ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)

@[expose] def ctxXi (t tau x₁ x₂ rho : G) : Subgroup G :=
  ⁅ctxOK t tau x₁ x₂ rho, zpowers rho⁆

variable [Finite G]

structure Ctx18S (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) (𝒮 : Subgroup G) : Prop
    extends Ctx13 t L S x₁ x₂ lam rho tau om where
  sylow : IsSylowIn 2 𝒮 (ctxK t tau x₁ x₂ rho)
  U_le : ctxU t tau x₁ x₂ lam ≤ 𝒮

structure Ctx18 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) (𝒮 : Subgroup G) : Prop
    extends Ctx18S t L S x₁ x₂ lam rho tau om 𝒮 where
  P_eq : ctxP t tau x₁ x₂ rho = ctxQ t tau x₁ x₂ rho

structure Ctx18B (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) (𝒮 : Subgroup G) : Prop
    extends Ctx18 t L S x₁ x₂ lam rho tau om 𝒮 where
  card_C : Nat.card (ctxCY t tau x₁ x₂ rho) = 2 ^ 10

end CFSG.OddStandard.SmallF3.HarrisU33
