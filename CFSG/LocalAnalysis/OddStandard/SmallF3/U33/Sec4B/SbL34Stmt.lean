module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def ctxLO (t tau x₁ x₂ : G) : Subgroup G :=
  normalizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G)

@[expose] def ctxPL (t tau x₁ x₂ : G) : Subgroup G :=
  ctxLO t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)

@[expose] def IsZ4Z4Grp (H : Subgroup G) : Prop := Nonempty (↥H ≃* Z4Z4)

@[expose] def IsE16Grp (H : Subgroup G) : Prop :=
  CFSG.Open.IsElemAbelian 2 H ∧ Nat.card H = 16

structure Ctx4L (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx4Q t L S x₁ x₂ lam rho tau where
  Q_inf : ctxQ t tau x₁ x₂ rho ⊓ closure {t, tau} = ⊥
  Z_Q : ctxQ t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) =
    fourGrp x₁ x₂
  Z_O : ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) =
    fourGrp x₁ x₂
  O_comm : ⁅ctxO t tau x₁ x₂, ctxO t tau x₁ x₂⁆ = fourGrp x₁ x₂
  comm_t : ⁅ctxQ t tau x₁ x₂ rho, zpowers t⁆ = fourGrp x₁ x₂
  comm_tau : ⁅ctxQ t tau x₁ x₂ rho, zpowers tau⁆ = fourGrp x₁ x₂
  comm_ttau : ⁅ctxQ t tau x₁ x₂ rho, zpowers (t * tau)⁆ = fourGrp x₁ x₂
  normal_base_U : NormalIn (baseGrp x₁ x₂) (ctxU t tau x₁ x₂ lam)
  tauU : conjIn (ctxU t tau x₁ x₂ lam) tau = tau • (fourGrp x₁ x₂ : Set G)
  ttauU : conjIn (ctxU t tau x₁ x₂ lam) (t * tau) = (t * tau) • (fourGrp x₁ x₂ : Set G)
  char_V : CharIn (fourGrp x₁ x₂) (ctxU t tau x₁ x₂ lam)
  char_O : CharIn (ctxO t tau x₁ x₂) (ctxU t tau x₁ x₂ lam)
  U_not_sylow : ¬ IsSylowIn 2 (ctxU t tau x₁ x₂ lam) (⊤ : Subgroup G)
  normal_CQtau : NormalIn (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G))
    (ctxM t tau x₁ x₂)
  normal_CQttau : NormalIn (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G))
    (ctxM t tau x₁ x₂)
  card_CQ_tl : Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G) : Subgroup G) = 8
  CU_tl : ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) =
    (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) ⊔ closure {t, tau, lam}
  card_CU_tl : Nat.card (ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G) : Subgroup G) =
    2 ^ 6
  tG_N : ∀ g : G, ∀ u ∈ ctxN tau x₁ x₂, g * t * g⁻¹ ≠ u
  tG_tN : ∀ g : G, ∀ u ∈ ctxN (t * tau) x₁ x₂, g * t * g⁻¹ ≠ u
  inv_tl : ∀ u ∈ fourGrp x₁ x₂, (t * lam * u) * (t * lam * u) = 1 →
    ∃ g : G, g * t * g⁻¹ = t * lam * u
  inv_l : ∀ u ∈ fourGrp x₁ x₂, (lam * u) * (lam * u) = 1 →
    ∃ g : G, g * (x₁ * x₂) ^ 2 * g⁻¹ = lam * u
  inv_tltau : ∀ u ∈ fourGrp x₁ x₂, (t * lam * tau * u) * (t * lam * tau * u) = 1 →
    ∃ g : G, g * (t * tau) * g⁻¹ = t * lam * tau * u
  inv_ltau : ∀ u ∈ fourGrp x₁ x₂, (lam * tau * u) * (lam * tau * u) = 1 →
    ∃ g : G, g * tau * g⁻¹ = lam * tau * u

structure Ctx4V (t x₁ x₂ lam tau : G) (W : Subgroup G) (v : G) : Prop where
  sylow : IsSylowIn 2 W (ctxLO t tau x₁ x₂)
  U_le : ctxU t tau x₁ x₂ lam ≤ W
  v_mem : v ∈ W
  v_norm : v ∈ normalizer ((ctxU t tau x₁ x₂ lam : Subgroup G) : Set G)
  v_not_mem : v ∉ ctxU t tau x₁ x₂ lam
  v_sq : v ^ 2 ∈ ctxU t tau x₁ x₂ lam
  v_cent_tl : v * (t * lam) = (t * lam) * v
  v_cent_V : ∀ a ∈ fourGrp x₁ x₂, v * a = a * v

structure Ctx4A (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx4L t L S x₁ x₂ lam rho tau where
  CG_O : centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) = fourGrp x₁ x₂
  CL_Obar : ∀ g ∈ ctxLO t tau x₁ x₂,
    (∀ o ∈ ctxO t tau x₁ x₂, g * o * g⁻¹ * o⁻¹ ∈ fourGrp x₁ x₂) → g ∈ ctxO t tau x₁ x₂
  card_CQ_tau : Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G) : Subgroup G) = 2 ^ 4
  card_CQ_ttau : Nat.card (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) : Subgroup G) =
    2 ^ 4
  CQ_t_tau : ctxQ t tau x₁ x₂ rho ⊓ centralizer ((closure {t, tau} : Subgroup G) : Set G) =
    fourGrp x₁ x₂
  CQ_tau_type : IsZ4Z4Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G)) ∨
    IsE16Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G))
  CQ_ttau_type : IsZ4Z4Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)) ∨
    IsE16Grp (ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G))
  CO_base : ctxO t tau x₁ x₂ ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) =
    closure {t, x₁, x₂}

structure Ctx4P (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop extends
    Ctx4A t L S x₁ x₂ lam rho tau where
  card_L : Nat.card (ctxLO t tau x₁ x₂) = 3 * 2 ^ 11
  P_core : CFSG.Open.pCoreOf 2 (ctxLO t tau x₁ x₂) = ctxPL t tau x₁ x₂
  L_eq : ctxLO t tau x₁ x₂ = ctxPL t tau x₁ x₂ ⊔ closure {rho, lam * t}
  O_le_P : ctxO t tau x₁ x₂ ≤ ctxPL t tau x₁ x₂
  card_P : Nat.card (ctxPL t tau x₁ x₂) = 2 ^ 10
  P_quot : (∀ p ∈ ctxPL t tau x₁ x₂, p ^ 2 ∈ ctxO t tau x₁ x₂) ∧
    ∀ p ∈ ctxPL t tau x₁ x₂, ∀ q ∈ ctxPL t tau x₁ x₂,
      p * q * p⁻¹ * q⁻¹ ∈ ctxO t tau x₁ x₂
  CP_rho : ctxPL t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) = closure {t, tau}
  X_not_normal_P : ¬ NormalIn (ctxX t tau x₁ x₂) (ctxPL t tau x₁ x₂)
  syl_P : IsSylowIn 2 (ctxPL t tau x₁ x₂ ⊔ zpowers (lam * t)) (ctxLO t tau x₁ x₂)
  Z_P : ∃ A : Subgroup G, fourGrp x₁ x₂ ≤ A ∧ A ≤ ctxPL t tau x₁ x₂ ∧
    4 * Nat.card (fourGrp x₁ x₂) ≤ Nat.card A ∧
    ∀ a ∈ A, ∀ q ∈ ctxPL t tau x₁ x₂, a * q * a⁻¹ * q⁻¹ ∈ fourGrp x₁ x₂

@[expose] def L34S0Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4Q t L S x₁ x₂ lam rho tau →
      Ctx4Q t L S x₁ x₂ lam rho (t * tau) → IsSylSL34 (ctxQ t tau x₁ x₂ rho) →
        Ctx4L t L S x₁ x₂ lam rho tau

@[expose] def L34S1Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4L t L S x₁ x₂ lam rho tau →
      ∃ (W : Subgroup G) (v : G), Ctx4V t x₁ x₂ lam tau W v

@[expose] def L34S2Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4L t L S x₁ x₂ lam rho tau →
      Ctx4A t L S x₁ x₂ lam rho tau

@[expose] def L34S3Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    {W : Subgroup G} {v : G},
    Sec4Glob G → Sec4BInputs → Ctx4A t L S x₁ x₂ lam rho tau → Ctx4V t x₁ x₂ lam tau W v →
      Ctx4P t L S x₁ x₂ lam rho tau

@[expose] def L34S4Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4P t L S x₁ x₂ lam rho tau →
      ¬ NormalIn (ctxQ t tau x₁ x₂ rho) (ctxLO t tau x₁ x₂)

@[expose] def L34S5Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Sec4Glob G → Sec4BInputs → Ctx4P t L S x₁ x₂ lam rho tau →
      ¬ NormalIn (ctxQ t tau x₁ x₂ rho) (ctxLO t tau x₁ x₂) →
        ∃ ω : G, (ω = tau ∨ ω = t * tau) ∧ NormalIn (ctxN ω x₁ x₂) (ctxLO t tau x₁ x₂)

@[expose] def L34S6Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    {W : Subgroup G} {v : G},
    Sec4Glob G → Sec4BInputs → Ctx4L t L S x₁ x₂ lam rho tau → Ctx4V t x₁ x₂ lam tau W v →
      ∀ ω : G, (ω = tau ∨ ω = t * tau) →
        NormalIn (ctxN ω x₁ x₂) (ctxLO t tau x₁ x₂) → False

end CFSG.OddStandard.SmallF3.HarrisU33
