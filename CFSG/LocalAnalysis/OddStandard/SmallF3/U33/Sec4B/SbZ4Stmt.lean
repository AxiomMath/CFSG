module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def ctxNQ (t tau x₁ x₂ rho : G) : Subgroup G :=
  normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)

@[expose] def ctxCQ (t tau x₁ x₂ rho : G) : Subgroup G :=
  centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)

@[expose] def Ctx4ZV (t tau x₁ x₂ lam rho : G) (V' : Subgroup G) (v₁ v₂ : G) : Prop :=
  CFSG.Open.IsElemAbelian 2 V' ∧ Nat.card V' = 4 ∧
  ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ ⊔ V' ∧ baseGrp x₁ x₂ ⊓ V' = ⊥ ∧
  ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ ⊔ V' ∧
  rho ∈ normalizer (V' : Set G) ∧
  v₁ ∈ V' ∧ v₂ ∈ V' ∧ v₁ ≠ 1 ∧ v₂ ∉ zpowers v₁ ∧ V' = closure {v₁, v₂} ∧
  t * v₁ * t⁻¹ = v₁ * x₁ ^ 2 ∧ t * v₂ * t⁻¹ = v₂ * x₂ ^ 2 ∧
  (lam * t) * v₁ * (lam * t)⁻¹ = v₂ ∧
  ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) = closure {x₁ * v₁, x₂ * v₂}

structure Ctx4Z (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx4Q t L S x₁ x₂ lam rho tau where
  q_iso : IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho)
  CQ_t : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = baseGrp x₁ x₂
  tQ : conjIn (ctxQ t tau x₁ x₂ rho) t = t • (fourGrp x₁ x₂ : Set G)
  tauQ : conjIn (ctxQ t tau x₁ x₂ rho) tau = tau • (fourGrp x₁ x₂ : Set G)
  ttauQ : conjIn (ctxQ t tau x₁ x₂ rho) (t * tau) = (t * tau) • (fourGrp x₁ x₂ : Set G)
  data_V : ∃ (V' : Subgroup G) (v₁ v₂ : G), Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂
  tau_cent_Y : ∀ a ∈ ctxYq t tau x₁ x₂ rho, tau * a = a * tau
  cent_M_Y : ctxM t tau x₁ x₂ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
    ctxQ t tau x₁ x₂ rho ⊔ zpowers tau
  tau_inv_Q : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹
  center_Qtau : (ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) ⊓
      centralizer ((ctxQ t tau x₁ x₂ rho ⊔ zpowers tau : Subgroup G) : Set G) =
    ctxYq t tau x₁ x₂ rho
  tG_Qtau : ∀ g : G, ∀ u ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau, g * t * g⁻¹ ≠ u
  U_not_sylow_L : ¬ IsSylowIn 2 (ctxU t tau x₁ x₂ lam) (ctxNQ t tau x₁ x₂ rho)
  tt_sylow : IsSylowIn 2 (closure {t, tau})
    (ctxNQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G))

@[expose] def L411ZSetupStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4Q t L S x₁ x₂ lam rho tau →
      Ctx4Q t L S x₁ x₂ lam rho (t * tau) → IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho) →
        Ctx4Z t L S x₁ x₂ lam rho tau ∨ Ctx4Z t L S x₁ x₂ lam rho (t * tau)

@[expose] def L411ZInSylStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4Z t L S x₁ x₂ lam rho tau →
      IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho) → False

@[expose] def L411ZNotSylStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4Z t L S x₁ x₂ lam rho tau →
      ¬ IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho) → False

end CFSG.OddStandard.SmallF3.HarrisU33
