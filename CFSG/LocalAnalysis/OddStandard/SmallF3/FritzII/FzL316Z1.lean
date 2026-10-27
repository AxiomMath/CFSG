module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure FzZ8 (Z E P : Subgroup G) : Prop where
  comm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  om1 : ∀ p ∈ P, p ^ 2 = 1 → p ∈ Z
  om2 : ∀ p ∈ P, p ^ 4 = 1 → p ∈ E
  sq : ∀ e ∈ E, ∃ p ∈ P, p ^ 2 = e

private lemma fzl_sq_mem_P_of_invol {t tau rho : G} {E W Q T P : Subgroup G}
    (hPf : FzPFacts t tau rho E W Q T P) {y p : G} (hyT : y ∈ T) (hy2 : y ^ 2 = 1)
    (hp : p ∈ P) : (y * p) ^ 2 ∈ P := by
  have key : (y * p) ^ 2 = (y * p * y⁻¹) * p := by
    have h1 : (y * p) ^ 2 = (y * p * y⁻¹) * (y * y) * p := by
      rw [pow_two]; group
    rw [h1, ← pow_two, hy2, mul_one]
  rw [key]
  exact P.mul_mem (hPf.nrm_P y hyT p hp) hp

private lemma fzl_sq_mem_P_of_invol_Q {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P)
    {x q : G} (hxT : x ∈ T) (hx2 : x ^ 2 = 1) (hxt : x * t = t * x) (hq : q ∈ Q) :
    (x * q) ^ 2 ∈ P := by
  have htT : t ∈ T := h.RT (h.QR (h.WQ h.t_mem))
  rcases hPf.Q_eq q hq with hqP | htqP
  · exact fzl_sq_mem_P_of_invol hPf hxT hx2 hqP
  · have hxt2 : (x * t) ^ 2 = 1 := by
      have hc : Commute x t := hxt
      rw [hc.mul_pow 2, hx2, h.t_sq, mul_one]
    have htt : t * (t * q) = q := by
      rw [← mul_assoc, ← pow_two, h.t_sq, one_mul]
    have heq : x * q = (x * t) * (t * q) := by
      rw [mul_assoc, htt]
    rw [heq]
    exact fzl_sq_mem_P_of_invol hPf (T.mul_mem hxT htT) hxt2 htqP

theorem fzl_sq_mem_P {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P) :
    ∀ g ∈ T, g ^ 2 ∈ P := by
  have hcomm_tau_t : tau * t = t * tau := by
    calc tau * t = (tau * t * tau⁻¹) * tau := by group
      _ = t * tau := by rw [h.tau_t]
  have hcomm_lam_t : lam * t = t * lam := by
    calc lam * t = (lam * t * lam⁻¹) * lam := by group
      _ = t * lam := by rw [h.lam_t]
  intro g hg
  rcases fzl_T_gen h g hg with hgQ | hgQ | hgQ | hgQ
  · rw [← one_mul g]
    exact fzl_sq_mem_P_of_invol_Q h hPf T.one_mem (one_pow 2)
      (by rw [one_mul, mul_one]) hgQ
  · have heq : g = tau * (tau⁻¹ * g) := by group
    rw [heq]
    exact fzl_sq_mem_P_of_invol_Q h hPf (h.RT h.tau_R) hPf.tau_sq1 hcomm_tau_t hgQ
  · have heq : g = lam * (lam⁻¹ * g) := by group
    rw [heq]
    exact fzl_sq_mem_P_of_invol_Q h hPf h.lam_T h.lam_sq hcomm_lam_t hgQ
  · have heq : g = (lam * tau) * ((lam * tau)⁻¹ * g) := by group
    rw [heq]
    refine fzl_sq_mem_P_of_invol_Q h hPf (T.mul_mem h.lam_T (h.RT h.tau_R)) ?_ ?_ hgQ
    · have hc : Commute lam tau := h.tau_lam.symm
      rw [hc.mul_pow 2, h.lam_sq, hPf.tau_sq1, mul_one]
    · calc (lam * tau) * t = lam * (tau * t) := by rw [mul_assoc]
        _ = lam * (t * tau) := by rw [hcomm_tau_t]
        _ = (lam * t) * tau := by rw [mul_assoc]
        _ = (t * lam) * tau := by rw [hcomm_lam_t]
        _ = t * (lam * tau) := by rw [mul_assoc]

theorem fzl_comm_mem_P {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P) :
    ∀ g ∈ T, ∀ g' ∈ T, ⁅g, g'⁆ ∈ P := by
  intro g hg g' hg'
  refine fzl_comm_mem_of_sq (fzl_sq_mem_P h hPf g hg) (fzl_sq_mem_P h hPf g' hg')
    (fzl_sq_mem_P h hPf (g * g') (T.mul_mem hg hg')) ?_
  intro n hn
  simpa using hPf.nrm_P g'⁻¹ (T.inv_mem hg') n hn

theorem fzl_phi_T_le_P {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P) :
    fzlPhi T ≤ P :=
  fzl_phi_le_of_elem (fzl_comm_mem_P h hPf) (fzl_sq_mem_P h hPf)

theorem fzl_phi_R_le_P {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) (hPf : FzPFacts t tau rho E W Q T P) :
    fzlPhi R ≤ P :=
  le_trans (fzl_phi_mono h.RT) (fzl_phi_T_le_P h hPf)

end CFSG.OddStandard.SmallF3.FritzII
