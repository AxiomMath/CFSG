module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

structure FzbsStr {G : Type} [Group G] (t q tau lam rho u : G) (Z E X W R T : Subgroup G) :
    Prop where
  ZE : Z ≤ E
  EX : E ≤ X
  XW : X ≤ W
  WR : W ≤ R
  RT : R ≤ T
  card_Z : Nat.card Z = 4
  card_E : Nat.card E = 16
  Z_sq : ∀ z ∈ Z, z ^ 2 = 1
  E_sq : ∀ e ∈ E, e ^ 2 ∈ Z
  W_comm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
  W_invol : ∀ w ∈ W, w ^ 2 = 1 → w ∈ Z ∨ t * w ∈ Z
  X_iff : ∀ w ∈ W, w ∈ X ↔ w ^ 2 ∈ Z
  t_mem : t ∈ X
  t_sq : t ^ 2 = 1
  t_notin_E : t ∉ E
  X_split : ∀ x ∈ X, x ∈ E ∨ t * x ∈ E
  q_mem : q ∈ W
  q_sq : q ^ 2 = t
  W_split : ∀ w ∈ W, w ∈ X ∨ q * w ∈ X
  pgroup_R : IsPGroup 2 R
  R_W : ∀ r ∈ R, ∀ w ∈ W, r * w * r⁻¹ ∈ W
  R_X : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ ∈ X
  R_Z : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ = z
  R_t : ∀ r ∈ R, t * (r * t * r⁻¹) ∈ Z
  R_t_surj : ∀ z ∈ Z, ∃ r ∈ R, r * t * r⁻¹ = t * z
  R_fix_t : ∀ r ∈ R, r * t * r⁻¹ = t → r ∈ W ∨ r * tau⁻¹ ∈ W
  R_comm : ∀ r ∈ R, ∀ r' ∈ R, ⁅r, r'⁆ ∈ W
  R_sq : ∀ r ∈ R, r ^ 2 ∈ W
  tau_R : tau ∈ R
  tau_t : tau * t * tau⁻¹ = t
  tau_X : ∀ x ∈ X, tau * x * tau⁻¹ = x⁻¹
  tau_q : tau * q * tau⁻¹ = q ∨ tau * q * tau⁻¹ = q⁻¹
  tau_sq : tau ^ 2 ∈ zpowers q
  tau_rho : tau * rho = rho * tau
  tau_lam : tau * lam = lam * tau
  rho_cube : rho ^ 3 = 1
  rho_R : ∀ r ∈ R, rho * r * rho⁻¹ ∈ R
  rho_W : ∀ w ∈ W, rho * w * rho⁻¹ ∈ W
  rho_X : ∀ x ∈ X, rho * x * rho⁻¹ ∈ X
  rho_E : ∀ e ∈ E, rho * e * rho⁻¹ ∈ E
  rho_Z : ∀ z ∈ Z, rho * z * rho⁻¹ ∈ Z
  rho_Z_fpf : ∀ z ∈ Z, z ≠ 1 → rho * z * rho⁻¹ ≠ z
  rho_t : rho * t * rho⁻¹ = t
  rho_q : rho * q * rho⁻¹ = q
  rho_W_fix : ∀ w ∈ W, rho * w * rho⁻¹ = w → w ∈ zpowers q
  E_rho : ⁅W, zpowers rho⁆ = E
  lam_T : lam ∈ T
  lam_sq : lam ^ 2 = 1
  lam_t : lam * t * lam⁻¹ = t
  lam_q : lam * q * lam⁻¹ = q
  lam_rho : lam * rho * lam⁻¹ = rho⁻¹
  lam_R : ∀ r ∈ R, lam * r * lam⁻¹ ∈ R
  u_mem : u ∈ E
  u_lam : lam * u * lam⁻¹ = u
  u_sq_ne : u ^ 2 ≠ 1
  lam_E_fix : ∀ e ∈ E, lam * e * lam⁻¹ = e → e ∈ zpowers u
  lam_X_inv : ∀ x ∈ X, lam * x * lam⁻¹ = x⁻¹ →
    ∃ e ∈ E, x = e * (lam * e * lam⁻¹)⁻¹ ∨ x = t * (e * (lam * e * lam⁻¹)⁻¹)
  lam_not_conj : ∀ g : G, g * lam * g⁻¹ ≠ t * lam
  T_cases : ∀ g ∈ T, g ∈ R ∨ lam * g ∈ R

structure FzbsOut {G : Type} [Group G] (t q tau lam rho : G) (Z E T P : Subgroup G) (s : G) :
    Prop where
  P_le : P ≤ T
  P_norm : ∀ g ∈ T, ∀ p ∈ P, g * p * g⁻¹ ∈ P
  card_P : Nat.card P = 64
  P_iso : Nonempty (↥P ≃* SylSL3_4)
  E_le_P : E ≤ P
  rho_norm : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P
  rho_fpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1
  cent_t : P ⊓ centralizer ({t} : Set G) = E
  s_cases : s = tau ∨ s = q * tau
  s_comm_P : ∀ p ∈ P, ⁅s, p⁆ ∈ Z
  gen : T = P ⊔ closure {q, s, lam}

end CFSG.OddStandard.SmallF3.FritzII
