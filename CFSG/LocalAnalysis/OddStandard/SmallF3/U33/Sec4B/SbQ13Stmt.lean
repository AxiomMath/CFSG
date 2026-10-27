module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbStmt2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def q13A (t tau x₁ x₂ rho : G) : Subgroup G :=
  ctxQ t tau x₁ x₂ rho ⊓ centralizer ({tau} : Set G)

@[expose] def q13P (t tau x₁ x₂ rho om : G) : Subgroup G :=
  q13A t tau x₁ x₂ rho ⊔ zpowers (t * om)

@[expose] def q13E0 (t tau x₁ x₂ rho om : G) : Subgroup G :=
  q13P t tau x₁ x₂ rho om ⊔ zpowers t

@[expose] def q13L (t tau x₁ x₂ rho om : G) : Subgroup G :=
  normalizer ((q13E0 t tau x₁ x₂ rho om : Subgroup G) : Set G)

@[expose] def q13B (t tau x₁ x₂ rho om : G) : Subgroup G :=
  q13L t tau x₁ x₂ rho om ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)

variable [Finite G]

structure Q13Ctx (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop where
  glob : Sec4Glob G
  c11 : Ctx11 t L S x₁ x₂ lam rho tau
  c12 : Lemma4_12Concl t tau x₁ x₂ lam rho
  syl : IsSylSL34 (ctxQ t tau x₁ x₂ rho)

structure Q13A (t : G) (x₁ x₂ lam rho tau om : G) : Prop where
  om_sq : om ^ 2 = 1
  om_not_mem : om ∉ closure {t, tau}
  t_om : om * t * om⁻¹ = t * tau
  CO_eq : ctxCO t tau x₁ x₂ rho = closure {t, om}
  X_om : ctxX t tau x₁ x₂ ⊓ centralizer ({om} : Set G) = ctxN tau x₁ x₂
  U_eq : ctxU t tau x₁ x₂ lam = ctxQ t tau x₁ x₂ rho ⊔ closure {t, om} ⊔ zpowers lam
  Q_comm : ⁅ctxQ t tau x₁ x₂ rho, ctxQ t tau x₁ x₂ rho⁆ = fourGrp x₁ x₂
  Q_fpf : ∀ g ∈ ctxQ t tau x₁ x₂ rho, rho * g = g * rho → g = 1
  CQt_ne : baseGrp x₁ x₂ ≠ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)
  CQt_om : ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ∈ baseGrp x₁ x₂ ↔
    om * a * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G)
  tauQ : conjIn (ctxQ t tau x₁ x₂ rho) tau = tau • (fourGrp x₁ x₂ : Set G)
  card_A : Nat.card (q13A t tau x₁ x₂ rho) = 2 ^ 4
  V_le_A : fourGrp x₁ x₂ ≤ q13A t tau x₁ x₂ rho
  A_iso : IsZ4pow 2 (q13A t tau x₁ x₂ rho)
  A_inv : ∀ a ∈ q13A t tau x₁ x₂ rho, rho * a * rho⁻¹ ∈ q13A t tau x₁ x₂ rho ∧
    lam * a * lam⁻¹ ∈ q13A t tau x₁ x₂ rho ∧ om * a * om⁻¹ ∈ q13A t tau x₁ x₂ rho
  t_inv_A : ∀ a ∈ q13A t tau x₁ x₂ rho, t * a * t⁻¹ = a⁻¹
  A_dich : closure {t, om} ⊓ centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) =
      closure {tau, om} ∨
    closure {t, om} ⊓ centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) =
      zpowers (t * om)
  lam_om : lam * om * lam⁻¹ = om ∨ lam * om * lam⁻¹ = om * tau
  card_CQ_tlam : Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) = 8
  card_CA_tlam : Nat.card ↥(q13A t tau x₁ x₂ rho ⊓ centralizer ({t * lam} : Set G)) = 4

structure Q13B (t : G) (x₁ x₂ tau : G) (𝒮 : Subgroup G) : Prop where
  Z_eq : 𝒮 ⊓ centralizer ((𝒮 : Subgroup G) : Set G) = zpowers ((x₁ * x₂) ^ 2)
  V_normal : NormalIn (fourGrp x₁ x₂) 𝒮
  V_unique : ∀ F : Subgroup G, NormalIn F 𝒮 → CFSG.Open.IsElemAbelian 2 F → Nat.card F = 4 →
    F = fourGrp x₁ x₂
  N_normal : NormalIn (ctxN tau x₁ x₂) 𝒮
  N_unique : ∀ F : Subgroup G, NormalIn F 𝒮 → CFSG.Open.IsElemAbelian 2 F → Nat.card F = 8 →
    F = ctxN tau x₁ x₂
  tG_N : ∀ g : G, g * t * g⁻¹ ∉ ctxN tau x₁ x₂

@[expose] def Q13Bs (t : G) (x₁ x₂ lam tau : G) : Prop :=
  ∀ 𝒮 : Subgroup G, IsPGroup 2 𝒮 → ctxU t tau x₁ x₂ lam ≤ 𝒮 → Q13B t x₁ x₂ tau 𝒮

structure Q13C (t : G) (x₁ x₂ lam tau om : G) : Prop where
  lam_om : lam * om * lam⁻¹ = om
  card_CU : Nat.card (↥(ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G))) = 2 ^ 6
  C_dih : closure {t, om} ⊓ centralizer ({t * lam} : Set G) = closure {t, tau}
  C_eq : ∀ 𝒮 : Subgroup G, IsPGroup 2 𝒮 → ctxU t tau x₁ x₂ lam ≤ 𝒮 →
    𝒮 ⊓ centralizer ({t * lam} : Set G) =
      ctxU t tau x₁ x₂ lam ⊓ centralizer ({t * lam} : Set G)

structure Q13D (t : G) (x₁ x₂ lam rho tau om : G) : Prop where
  A_cent : closure {t, om} ⊓ centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) =
    zpowers (t * om)
  gam_sq : (t * om) ^ 2 = tau
  P_iso : IsZ4pow 3 (q13P t tau x₁ x₂ rho om)
  t_inv_P : ∀ p ∈ q13P t tau x₁ x₂ rho om, t * p * t⁻¹ = p⁻¹
  E0_eq : ctxU t tau x₁ x₂ lam ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) =
    q13E0 t tau x₁ x₂ rho om
  P_char : CharIn (q13P t tau x₁ x₂ rho om) (q13E0 t tau x₁ x₂ rho om) ∧
    CharIn (q13E0 t tau x₁ x₂ rho om) (ctxU t tau x₁ x₂ lam)
  CP_rho : q13P t tau x₁ x₂ rho om ⊓ centralizer ({rho} : Set G) = zpowers (t * om)
  comm_P_rho : ⁅q13P t tau x₁ x₂ rho om, zpowers rho⁆ = q13A t tau x₁ x₂ rho
  rho_norm : rho ∈ q13L t tau x₁ x₂ rho om
  M_le_L : ctxM t tau x₁ x₂ ≤ q13L t tau x₁ x₂ rho om
  cent_E0 : centralizer ((q13E0 t tau x₁ x₂ rho om : Subgroup G) : Set G) = ctxN tau x₁ x₂
  tL : ∀ g ∈ q13L t tau x₁ x₂ rho om, g * t * g⁻¹ ∈ t • (q13P t tau x₁ x₂ rho om : Set G)
  CL_t : q13L t tau x₁ x₂ rho om ⊓ centralizer ({t} : Set G) =
    ctxM t tau x₁ x₂ ⊓ centralizer ({t} : Set G)
  rho_syl3 : IsSylowIn 3 (zpowers rho) (q13L t tau x₁ x₂ rho om)
  L_card : Nat.card (q13L t tau x₁ x₂ rho om) = 3 * 2 ^ 11 ∨
    Nat.card (q13L t tau x₁ x₂ rho om) = 3 * 2 ^ 12 ∨
    Nat.card (q13L t tau x₁ x₂ rho om) = 3 * 2 ^ 13
  B_two : IsPGroup 2 (q13B t tau x₁ x₂ rho om)
  B_normal : NormalIn (q13B t tau x₁ x₂ rho om) (q13L t tau x₁ x₂ rho om)
  E0_le_B : q13E0 t tau x₁ x₂ rho om ≤ q13B t tau x₁ x₂ rho om
  L_eq : q13L t tau x₁ x₂ rho om = q13B t tau x₁ x₂ rho om ⊔ closure {x₁, x₂, rho, lam}

@[expose] def Q13FamA : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (_hq : Q13Ctx t L S x₁ x₂ lam rho tau), ∃ om : G, Q13A t x₁ x₂ lam rho tau om

@[expose] def Q13FamB : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}
    (_hq : Q13Ctx t L S x₁ x₂ lam rho tau) (_hA : Q13A t x₁ x₂ lam rho tau om),
    Q13Bs t x₁ x₂ lam tau

@[expose] def Q13FamC : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}
    (_hq : Q13Ctx t L S x₁ x₂ lam rho tau) (_hA : Q13A t x₁ x₂ lam rho tau om)
    (_hB : Q13Bs t x₁ x₂ lam tau), Q13C t x₁ x₂ lam tau om

@[expose] def Q13FamD : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}
    (_hq : Q13Ctx t L S x₁ x₂ lam rho tau) (_hA : Q13A t x₁ x₂ lam rho tau om)
    (_hB : Q13Bs t x₁ x₂ lam tau) (_hC : Q13C t x₁ x₂ lam tau om),
    Q13D t x₁ x₂ lam rho tau om

@[expose] def Q13FamE : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}
    (_hq : Q13Ctx t L S x₁ x₂ lam rho tau) (_hA : Q13A t x₁ x₂ lam rho tau om)
    (_hB : Q13Bs t x₁ x₂ lam tau) (_hC : Q13C t x₁ x₂ lam tau om)
    (_hD : Q13D t x₁ x₂ lam rho tau om), False

theorem lemma4_13_of_families (hA : Q13FamA) (hB : Q13FamB) (hC : Q13FamC) (hD : Q13FamD)
    (hE : Q13FamE) : Lemma4_13Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau hG hc h12
  rcases h12.1.2.2.2.2.2.2 with h | h
  · exact h
  · exfalso
    have hq : Q13Ctx t L S x₁ x₂ lam rho tau := ⟨hG, hc, h12, h⟩
    obtain ⟨om, hAom⟩ := hA hq
    have hBs : Q13Bs t x₁ x₂ lam tau := hB hq hAom
    have hCs := hC hq hAom hBs
    have hDs := hD hq hAom hBs hCs
    exact hE hq hAom hBs hCs hDs

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
