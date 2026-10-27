module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def ctxWN (t tau x₁ x₂ rho : G) : Subgroup G :=
  ctxCQ t tau x₁ x₂ rho ⊓
    normalizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers t : Subgroup G) : Set G)

@[expose] def ctxE0N (t tau x₁ x₂ rho : G) : Subgroup G :=
  ctxWN t tau x₁ x₂ rho ⊔ zpowers tau

@[expose] def ctxVN (t tau x₁ x₂ lam rho : G) : Subgroup G :=
  ctxWN t tau x₁ x₂ rho ⊔ closure ({t, tau, lam} : Set G)

@[expose] def ctxQm (t tau x₁ x₂ rho : G) : Subgroup G :=
  ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)

structure ZNW (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx4Z t L S x₁ x₂ lam rho tau where
  Q_lt_W : ctxQ t tau x₁ x₂ rho < ctxWN t tau x₁ x₂ rho

end CFSG.OddStandard.SmallF3.HarrisU33
