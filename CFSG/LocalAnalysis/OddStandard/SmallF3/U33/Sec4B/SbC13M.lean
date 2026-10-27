module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13Defs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx13M (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) : Prop extends
    Ctx13D t L S x₁ x₂ lam rho tau om where
  phi_Q' : ctxPhi (ctxQ t tau x₁ x₂ rho) = fourGrp x₁ x₂
  data_V : ∃ (V' : Subgroup G) (v₁ v₂ : G), Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂
  tG_Qom : ∀ g : G, ∀ u ∈ ctxQ t tau x₁ x₂ rho ⊔ closure {om, tau}, g * t * g⁻¹ ≠ u
  cent_M_Y : ctxM t tau x₁ x₂ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
    ctxQ t tau x₁ x₂ rho ⊔ closure {tau, om}
  comm_Y : ⁅ctxQ t tau x₁ x₂ rho, zpowers om⁆ ⊔ ⁅ctxQ t tau x₁ x₂ rho, zpowers tau⁆ =
    ctxYq t tau x₁ x₂ rho
  cent_R : centralizer ((ctxR t tau x₁ x₂ : Subgroup G) : Set G) = fourGrp x₁ x₂
  K_le : ctxK t tau x₁ x₂ rho ≤
      normalizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G) ∧
    normalizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G) ≤
      normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) ∧
    normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) ≤
      normalizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G)
  M_le_K : ctxM t tau x₁ x₂ ≤ ctxK t tau x₁ x₂ rho
  U_le_K : ctxU t tau x₁ x₂ lam ≤ ctxK t tau x₁ x₂ rho
  normal_Q_K : NormalIn (ctxQ t tau x₁ x₂ rho) (ctxK t tau x₁ x₂ rho)

@[expose] def Ctx13KFacts (t : G) (x₁ x₂ lam rho tau om : G) : Prop :=
  Nat.card (ctxK t tau x₁ x₂ rho) = 3 * 2 ^ 12 ∧
  conjIn (ctxK t tau x₁ x₂ rho) t =
    InvIn (t • (ctxQ t tau x₁ x₂ rho : Set G)) ∪
      InvIn ((t * tau) • (ctxQ t tau x₁ x₂ rho : Set G)) ∧
  ctxK t tau x₁ x₂ rho = CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho) ⊔ closure {rho, lam} ∧
  ctxK t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = closure {t, om} ⊔ zpowers rho

@[expose] def Ctx13KStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}
    (hG : Sec4Glob G) (hc : Ctx13M t L S x₁ x₂ lam rho tau om),
    Ctx13KFacts t x₁ x₂ lam rho tau om

end CFSG.OddStandard.SmallF3.HarrisU33
