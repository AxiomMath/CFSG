module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbInputs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx4C (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx10 t L S x₁ x₂ lam rho tau where
  tM : conjIn (ctxM t tau x₁ x₂) t = t • (fourGrp x₁ x₂ : Set G)
  tG_X : ∀ g : G, g * t * g⁻¹ ∈ ctxX t tau x₁ x₂ →
    g * t * g⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G)
  normal_V : NormalIn (fourGrp x₁ x₂) (ctxM t tau x₁ x₂)
  normal_E : NormalIn (ctxE t x₁ x₂) (ctxM t tau x₁ x₂)
  normal_N : NormalIn (ctxN tau x₁ x₂) (ctxM t tau x₁ x₂)
  normal_tN : NormalIn (ctxN (t * tau) x₁ x₂) (ctxM t tau x₁ x₂)
  card_M : Nat.card (ctxM t tau x₁ x₂) = 3 * 2 ^ 9
  card_O : Nat.card (ctxO t tau x₁ x₂) = 2 ^ 8
  M_eq : ctxM t tau x₁ x₂ = ctxO t tau x₁ x₂ ⊔ closure {rho, lam}
  O_eq_R : ctxO t tau x₁ x₂ = ctxR t tau x₁ x₂
  O_eq_CV : ctxO t tau x₁ x₂ =
    ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
  O_quot : (∀ a ∈ ctxO t tau x₁ x₂, a ^ 2 ∈ ctxX t tau x₁ x₂) ∧
    ∀ a ∈ ctxO t tau x₁ x₂, ∀ b ∈ ctxO t tau x₁ x₂, a * b * a⁻¹ * b⁻¹ ∈ ctxX t tau x₁ x₂
  CO_rho : ctxCO t tau x₁ x₂ rho = closure {t, tau}
  tauM : conjIn (ctxM t tau x₁ x₂) tau = tau • (fourGrp x₁ x₂ : Set G)
  ttauM : conjIn (ctxM t tau x₁ x₂) (t * tau) = (t * tau) • (fourGrp x₁ x₂ : Set G)
  cent_E : ctxO t tau x₁ x₂ ⊓ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) =
    closure {t, tau, x₁, x₂}
  normal_centE : NormalIn (closure {t, tau, x₁, x₂}) (ctxM t tau x₁ x₂)
  normal_Q : NormalIn (ctxQ t tau x₁ x₂ rho) (ctxM t tau x₁ x₂)
  base_le_Q : baseGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho
  S_le_U : S ≤ ctxU t tau x₁ x₂ lam
  U_sylow : IsSylowIn 2 (ctxU t tau x₁ x₂ lam) (ctxM t tau x₁ x₂)

structure Ctx4Q (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx4C t L S x₁ x₂ lam rho tau where
  card_Q : Nat.card (ctxQ t tau x₁ x₂ rho) = 2 ^ 6
  O_eq_Q : ctxO t tau x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau}
  CQ_rho : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = ⊥
  Q_quot : (∀ a ∈ ctxQ t tau x₁ x₂ rho, a ^ 2 ∈ fourGrp x₁ x₂) ∧
    ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho,
      a * b * a⁻¹ * b⁻¹ ∈ fourGrp x₁ x₂
  dich : IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho) ∨ IsSylSL34 (ctxQ t tau x₁ x₂ rho)

@[expose] def L411FourStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx10 t L S x₁ x₂ lam rho tau →
      (conjIn (ctxM t tau x₁ x₂) t).ncard = 4 → Ctx4C t L S x₁ x₂ lam rho tau

@[expose] def L411QStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4C t L S x₁ x₂ lam rho tau → Ctx4Q t L S x₁ x₂ lam rho tau

@[expose] def L411SylStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4Q t L S x₁ x₂ lam rho tau →
      Ctx4Q t L S x₁ x₂ lam rho (t * tau) → IsSylSL34 (ctxQ t tau x₁ x₂ rho) → False

@[expose] def L411AbStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4Q t L S x₁ x₂ lam rho tau →
      Ctx4Q t L S x₁ x₂ lam rho (t * tau) → IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho) → False

end CFSG.OddStandard.SmallF3.HarrisU33
