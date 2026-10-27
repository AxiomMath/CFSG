module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

structure FzStr {G : Type} [Group G] (t tau lam rho : G) (Z E W Q R T : Subgroup G) : Prop where
  ZE : Z ≤ E
  EW : E ≤ W
  WQ : W ≤ Q
  QR : Q ≤ R
  RT : R ≤ T
  card_Z : Nat.card Z = 4
  card_E : Nat.card E = 16
  card_W : Nat.card W = 32
  card_Q : Nat.card Q = 128
  card_R : Nat.card R = 256
  card_T : Nat.card T = 512
  pgroup_T : IsPGroup 2 T
  nrm_Z : ∀ g ∈ T, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z
  nrm_W : ∀ g ∈ T, ∀ w ∈ W, g * w * g⁻¹ ∈ W
  nrm_Q : ∀ g ∈ T, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q
  nrm_R : ∀ g ∈ T, ∀ r ∈ R, g * r * g⁻¹ ∈ R
  W_comm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a
  t_mem : t ∈ W
  t_sq : t ^ 2 = 1
  t_notin_E : t ∉ E
  W_split : ∀ w ∈ W, w ∈ E ∨ t * w ∈ E
  E_exp : ∀ e ∈ E, e ^ 4 = 1
  E_sq : ∀ e ∈ E, e ^ 2 ∈ Z
  Z_sq : ∀ z ∈ Z, z ^ 2 = 1
  Z_sqrt : ∀ z ∈ Z, ∃ e ∈ E, e ^ 2 = z
  E_invol : ∀ e ∈ E, e ^ 2 = 1 → e ∈ Z
  E_equiv : Nonempty (↥E ≃* Z4Z4)
  CW : ∀ g : G, (∀ w ∈ W, g * w = w * g) → g ∈ W
  R_comm : ∀ r ∈ R, ∀ r' ∈ R, ⁅r, r'⁆ ∈ W
  R_sq : ∀ r ∈ R, r ^ 2 ∈ W
  R_Z : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ = z
  T_t : ∀ g ∈ T, ∃ z ∈ Z, g * t * g⁻¹ = t * z
  Q_t : ∀ n ∈ Q, n ∉ W → n * t * n⁻¹ ≠ t
  tau_R : tau ∈ R
  tau_notin_Q : tau ∉ Q
  tau_t : tau * t * tau⁻¹ = t
  tau_W : ∀ w ∈ W, tau * w * tau⁻¹ = w⁻¹
  tau_sq : tau ^ 2 = 1 ∨ tau ^ 2 = t
  tau_Q : ∀ q ∈ Q, ⁅tau, q⁆ ∈ W
  tau_rho : tau * rho = rho * tau
  tau_lam : tau * lam = lam * tau
  lam_T : lam ∈ T
  lam_sq : lam ^ 2 = 1
  lam_t : lam * t * lam⁻¹ = t
  lam_Z : ∃ z ∈ Z, lam * z * lam⁻¹ ≠ z
  lam_E : (∀ e ∈ E, lam * e * lam⁻¹ ∈ E) ∧
    ∃ e ∈ E, lam * e * lam⁻¹ ≠ e ∧ lam * e * lam⁻¹ ≠ e⁻¹
  lam_Q : ∃ n ∈ Q, ⁅lam, n⁆ ∉ W
  lam_rho : lam * rho * lam⁻¹ = rho⁻¹
  rho_ord : rho ^ 3 = 1
  rho_t : rho * t * rho⁻¹ = t
  rho_nrm_Z : ∀ z ∈ Z, rho * z * rho⁻¹ ∈ Z
  rho_nrm_E : ∀ e ∈ E, rho * e * rho⁻¹ ∈ E
  rho_nrm_Q : ∀ q ∈ Q, rho * q * rho⁻¹ ∈ Q
  rho_Z : ∀ z ∈ Z, z ≠ 1 → rho * z * rho⁻¹ ≠ z
  rho_Q : ∀ q ∈ Q, rho * q * rho⁻¹ = q → q = 1 ∨ q = t
  rho_QW : ∀ q ∈ Q, rho * q * rho⁻¹ * q⁻¹ ∈ W → q ∈ W
  E_rho : ⁅W, zpowers rho⁆ = E

end CFSG.OddStandard.SmallF3.FritzII
