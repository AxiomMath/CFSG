module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma4_12aConcl (t tau x₁ x₂ rho : G) : Prop :=
  ctxPhi (ctxR t tau x₁ x₂) = fourGrp x₁ x₂ ∧
  NormalIn (baseGrp x₁ x₂) (ctxR t tau x₁ x₂) ∧
  ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = baseGrp x₁ x₂ ∧
  Nat.card (ctxQ t tau x₁ x₂ rho) = 2 ^ 6 ∧
  ctxR t tau x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊔ closure {t, tau} ∧
  ctxQ t tau x₁ x₂ rho = ⁅ctxR t tau x₁ x₂, zpowers rho⁆ ∧
  (IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho) ∨ IsSylSL34 (ctxQ t tau x₁ x₂ rho))

@[expose] def Lemma4_12bConcl (t tau x₁ x₂ lam rho : G) : Prop :=
  ctxM t tau x₁ x₂ =
    (ctxQ t tau x₁ x₂ rho ⊔ (ctxCO t tau x₁ x₂ rho ⊔ zpowers rho)) ⊔ zpowers lam

@[expose] def Lemma4_12Concl (t tau x₁ x₂ lam rho : G) : Prop :=
  Lemma4_12aConcl t tau x₁ x₂ rho ∧ Lemma4_12bConcl t tau x₁ x₂ lam rho

@[expose] def Lemma4_13Concl (t tau x₁ x₂ rho : G) : Prop :=
  IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho)

@[expose] def Ctx13V (t tau x₁ x₂ lam rho om : G) (V' : Subgroup G) (v₁ v₂ : G) : Prop :=
  CFSG.Open.IsElemAbelian 2 V' ∧ Nat.card V' = 4 ∧
  ctxQ t tau x₁ x₂ rho = baseGrp x₁ x₂ ⊔ V' ∧ baseGrp x₁ x₂ ⊓ V' = ⊥ ∧
  rho ∈ normalizer (V' : Set G) ∧ lam * t ∈ normalizer (V' : Set G) ∧
  ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ ⊔ V' ∧
  V' ⊓ centralizer ({lam * t} : Set G) = zpowers v₁ ∧ v₁ ∈ V' ∧ v₁ ≠ 1 ∧
  t * v₁ * t⁻¹ = v₁ * (x₁ * x₂) ^ 2 ∧
  v₂ ∈ V' ∧ v₂ ∉ zpowers v₁ ∧ V' = closure {v₁, v₂} ∧
  t * v₂ * t⁻¹ = v₂ * x₁ ^ 2 ∧ (lam * t) * v₂ * (lam * t)⁻¹ = v₂ * v₁ ∧
  ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) = closure {x₁ * v₂, x₂ * v₁ * v₂} ∧
  (∃ w ∈ fourGrp x₁ x₂, om * x₁ * om⁻¹ = x₁ * v₂ * w) ∧
  (∃ w ∈ fourGrp x₁ x₂, om * x₂ * om⁻¹ = x₂ * v₁ * v₂ * w)

@[expose] def Ctx13Om (t tau x₁ x₂ rho : G) (w : G) : Prop :=
  CFSG.Open.IsElemAbelian 2 ⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆ ∧
  Nat.card (⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆ : Subgroup G) = 4 ∧
  ⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆ ⊓ fourGrp x₁ x₂ = ⊥ ∧
  ctxQ t tau x₁ x₂ rho ⊓ centralizer ({w} : Set G) = ctxYq t tau x₁ x₂ rho ∧
  InvIn (w • (ctxQ t tau x₁ x₂ rho : Set G)) = w • (ctxYq t tau x₁ x₂ rho : Set G)

structure Ctx13 (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) : Prop extends
    Ctx11 t L S x₁ x₂ lam rho tau where
  q_iso : IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho)
  om_sq : om ^ 2 = 1
  om_not_mem : om ∉ closure {t, tau}
  CO_eq : ctxCO t tau x₁ x₂ rho = closure {t, om}
  t_om : om * t * om⁻¹ = t * tau
  lam_om : lam * om * lam⁻¹ = om
  O_cent : ctxO t tau x₁ x₂ = ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
  phi_Q' : ctxPhi (ctxQ t tau x₁ x₂ rho) = fourGrp x₁ x₂
  data_V : ∃ (V' : Subgroup G) (v₁ v₂ : G), Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂
  normal_Y : NormalIn (ctxYq t tau x₁ x₂ rho) (ctxM t tau x₁ x₂)
  Y_cent : ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = fourGrp x₁ x₂ ∧
    ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) = fourGrp x₁ x₂
  Y_comm : ⁅ctxYq t tau x₁ x₂ rho, zpowers t⁆ = fourGrp x₁ x₂ ∧
    ⁅ctxYq t tau x₁ x₂ rho, zpowers (t * tau)⁆ = fourGrp x₁ x₂
  tau_cent_Y : ∀ a ∈ ctxYq t tau x₁ x₂ rho, tau * a = a * tau
  tau_inv_Q : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹
  om_cent_Y : ∀ a ∈ ctxYq t tau x₁ x₂ rho, om * a = a * om
  tG_Qom : ∀ g : G, ∀ u ∈ ctxQ t tau x₁ x₂ rho ⊔ closure {om, tau}, g * t * g⁻¹ ≠ u
  cent_M_Y : ctxM t tau x₁ x₂ ⊓ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) =
    ctxQ t tau x₁ x₂ rho ⊔ closure {tau, om}
  Q_om : Ctx13Om t tau x₁ x₂ rho om
  Q_omtau : Ctx13Om t tau x₁ x₂ rho (om * tau)
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
  tK : conjIn (ctxK t tau x₁ x₂ rho) t =
    InvIn (t • (ctxQ t tau x₁ x₂ rho : Set G)) ∪
      InvIn ((t * tau) • (ctxQ t tau x₁ x₂ rho : Set G))
  U_le_K : ctxU t tau x₁ x₂ lam ≤ ctxK t tau x₁ x₂ rho
  card_K : Nat.card (ctxK t tau x₁ x₂ rho) = 3 * 2 ^ 12
  K_eq : ctxK t tau x₁ x₂ rho = CFSG.Open.pCoreOf 2 (ctxK t tau x₁ x₂ rho) ⊔ closure {rho, lam}
  normal_Q_K : NormalIn (ctxQ t tau x₁ x₂ rho) (ctxK t tau x₁ x₂ rho)
  CK_rho : ctxK t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = closure {t, om} ⊔ zpowers rho

end CFSG.OddStandard.SmallF3.HarrisU33
