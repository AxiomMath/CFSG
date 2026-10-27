module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XSq

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T : Subgroup G}

theorem fzr_x_conj_E [Finite G] (h : FzStr t tau lam rho Z E W Q R T) {q e : G} (hq : q ∈ Q)
    (he : e ∈ E) : e⁻¹ * (q * e * q⁻¹) ∈ Z := by
  have he' : q * e * q⁻¹ ∈ E := fzl_nrm_E h q (h.RT (h.QR hq)) e he
  apply h.E_invol _ (E.mul_mem (E.inv_mem he) he')
  have hcomm : Commute e⁻¹ (q * e * q⁻¹) :=
    h.W_comm _ (h.EW (E.inv_mem he)) _ (h.EW he')
  rw [hcomm.mul_pow, inv_pow, conj_pow, h.R_Z q (h.QR hq) _ (h.E_sq e he)]
  simp

theorem fzr_x_conj_t (h : FzStr t tau lam rho Z E W Q R T) {q : G} (hq : q ∈ Q) :
    ∃ z ∈ Z, (q * lam) * t * (q * lam)⁻¹ = t * z := by
  obtain ⟨z, hz, hzt⟩ := h.T_t q (h.RT (h.QR hq))
  refine ⟨z, hz, ?_⟩
  calc (q * lam) * t * (q * lam)⁻¹ = q * (lam * t * lam⁻¹) * q⁻¹ := by group
    _ = q * t * q⁻¹ := by rw [h.lam_t]
    _ = t * z := hzt

theorem fzr_x_conj_x12 [Finite G] (h : FzStr t tau lam rho Z E W Q R T) {q x1 x2 : G}
    (hq : q ∈ Q) (hx1 : x1 ∈ E) (hx2 : x2 ∈ E) (hlam : lam * x1 * lam⁻¹ = x2) :
    (∃ z ∈ Z, (q * lam) * x1 * (q * lam)⁻¹ = x2 * z) ∧
      ∃ z ∈ Z, (q * lam) * x2 * (q * lam)⁻¹ = x1 * z := by
  have hlam2 : lam * lam = 1 := by simpa [pow_two] using h.lam_sq
  have hinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hlam2
  have hlam' : lam * x2 * lam⁻¹ = x1 := by
    rw [← hlam]
    calc lam * (lam * x1 * lam⁻¹) * lam⁻¹ = (lam * lam) * x1 * (lam * lam)⁻¹ := by group
      _ = x1 := by rw [hlam2]; group
  refine ⟨⟨_, fzr_x_conj_E h hq hx2, ?_⟩, ⟨_, fzr_x_conj_E h hq hx1, ?_⟩⟩
  · calc (q * lam) * x1 * (q * lam)⁻¹ = q * (lam * x1 * lam⁻¹) * q⁻¹ := by group
      _ = x2 * (x2⁻¹ * (q * x2 * q⁻¹)) := by rw [hlam]; group
  · calc (q * lam) * x2 * (q * lam)⁻¹ = q * (lam * x2 * lam⁻¹) * q⁻¹ := by group
      _ = x1 * (x1⁻¹ * (q * x1 * q⁻¹)) := by rw [hlam']; group

theorem fzr_x_sq_mem [Finite G] (h : FzStr t tau lam rho Z E W Q R T)
    (hP : t ∈ ⁅Q, zpowers rho⁆) {q : G} (hq : q ∈ Q) (hqW : ⁅lam, q⁆ ∉ W) :
    (q * lam) ^ 2 ∈ Q ∧ (q * lam) ^ 2 ∉ W ∧ (q * lam) ^ 4 ∈ W ∧ (q * lam) ^ 4 ∉ E := by
  have hlam2 : lam * lam = 1 := by simpa [pow_two] using h.lam_sq
  have hinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hlam2
  have hqT : q ∈ T := h.RT (h.QR hq)
  have hq2 : q ^ 2 ∈ W := h.R_sq q (h.QR hq)
  have hn2 : (q * lam) ^ 2 = q * (lam * q * lam⁻¹) := by
    rw [pow_two, hinv]
    simp only [mul_assoc]
  have hQ : (q * lam) ^ 2 ∈ Q := by
    rw [hn2]
    exact Q.mul_mem hq (h.nrm_Q lam h.lam_T q hq)
  have hnW : (q * lam) ^ 2 ∉ W := by
    intro hW
    apply hqW
    have h1 : q * ⁅lam, q⁆ * q⁻¹ ∈ W := by
      have e : q * ⁅lam, q⁆ * q⁻¹ = (q * (lam * q * lam⁻¹)) * (q ^ 2)⁻¹ := by
        rw [commutatorElement_def]; group
      rw [e, ← hn2]
      exact W.mul_mem hW (W.inv_mem hq2)
    have h2 := h.nrm_W q⁻¹ (T.inv_mem hqT) _ h1
    have e2 : q⁻¹ * (q * ⁅lam, q⁆ * q⁻¹) * q⁻¹⁻¹ = ⁅lam, q⁆ := by group
    rwa [e2] at h2
  have h4 : (q * lam) ^ 4 = ((q * lam) ^ 2) ^ 2 := by rw [← pow_mul]
  refine ⟨hQ, hnW, ?_, ?_⟩
  · rw [h4]
    exact h.R_sq _ (h.QR hQ)
  · rw [h4]
    exact fzr_x_sq_notin_E h hP _ hQ hnW

theorem fzr_x_comm_tau (h : FzStr t tau lam rho Z E W Q R T) {q : G} (hq : q ∈ Q) :
    ∃ m ∈ W, (q * lam) * tau * (q * lam)⁻¹ = m * tau := by
  refine ⟨q * tau * q⁻¹ * tau⁻¹, ?_, ?_⟩
  · have e : q * tau * q⁻¹ * tau⁻¹ = (⁅tau, q⁆)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact W.inv_mem (h.tau_Q q hq)
  · have hl : lam * tau * lam⁻¹ = tau := by
      rw [mul_inv_eq_iff_eq_mul]
      exact h.tau_lam.symm
    calc (q * lam) * tau * (q * lam)⁻¹ = q * (lam * tau * lam⁻¹) * q⁻¹ := by group
      _ = q * tau * q⁻¹ := by rw [hl]
      _ = (q * tau * q⁻¹ * tau⁻¹) * tau := by group

end CFSG.OddStandard.SmallF3.FritzII
