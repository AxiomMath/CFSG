module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3Cos

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T : Subgroup G}

theorem fzr_x_exists_sq [Finite G] (h : FzStr t tau lam rho Z E W Q R T)
    (hP : t ∈ ⁅Q, zpowers rho⁆) : ∃ x ∈ Q, x ^ 2 ∉ E := by
  by_contra hcon
  push Not at hcon
  have hle : fzlPhi Q ≤ E := by
    refine fzl_phi_le_of_elem (fun a ha b hb => ?_) hcon
    refine fzl_comm_mem_of_sq (hcon a ha) (hcon b hb) (hcon _ (Q.mul_mem ha hb)) (fun n hn => ?_)
    simpa using fzl_nrm_E h b⁻¹ (h.RT (h.QR (Q.inv_mem hb))) n hn
  rw [fzl_phiQ_eq_W h hP] at hle
  exact h.t_notin_E (hle h.t_mem)

private theorem fzrAux_sq_mem_E (h : FzStr t tau lam rho Z E W Q R T) :
    ∀ w ∈ W, w ^ 2 ∈ E := by
  intro w hw
  rcases h.W_split w hw with hwE | htwE
  · simpa [pow_two] using E.mul_mem hwE hwE
  · have hcomm : Commute t w := h.W_comm t h.t_mem w hw
    have h2 : (t * w) ^ 2 = w ^ 2 := by
      rw [hcomm.mul_pow 2, h.t_sq, one_mul]
    have hmem : (t * w) ^ 2 ∈ E := by simpa [pow_two] using E.mul_mem htwE htwE
    rwa [h2] at hmem

private theorem fzrAux_rho_sq (h : FzStr t tau lam rho Z E W Q R T) : rho ^ 2 = rho⁻¹ := by
  have h' : rho ^ 2 * rho = 1 := by rw [← pow_succ, h.rho_ord]
  exact mul_eq_one_iff_eq_inv.mp h'

private theorem fzrAux_conj_inv_eq (hrho : rho ^ 3 = 1) (w : G) :
    rho * (rho * w * rho⁻¹) * rho⁻¹ = rho⁻¹ * w * rho := by
  have h2 : rho ^ 2 = rho⁻¹ := by
    have h' : rho ^ 2 * rho = 1 := by rw [← pow_succ, hrho]
    exact mul_eq_one_iff_eq_inv.mp h'
  calc rho * (rho * w * rho⁻¹) * rho⁻¹
      = rho ^ 2 * w * (rho ^ 2)⁻¹ := by rw [pow_two]; group
    _ = rho⁻¹ * w * (rho⁻¹)⁻¹ := by rw [h2]
    _ = rho⁻¹ * w * rho := by group

private theorem fzrAux_rho_inv_nrm_E (h : FzStr t tau lam rho Z E W Q R T) :
    ∀ e ∈ E, rho⁻¹ * e * rho ∈ E := by
  intro e he
  have h1 : rho * (rho * e * rho⁻¹) * rho⁻¹ ∈ E :=
    h.rho_nrm_E (rho * e * rho⁻¹) (h.rho_nrm_E e he)
  rwa [fzrAux_conj_inv_eq h.rho_ord e] at h1

private theorem fzrAux_rho_nrm_W (h : FzStr t tau lam rho Z E W Q R T) :
    ∀ w ∈ W, rho * w * rho⁻¹ ∈ W := by
  intro w hw
  rcases h.W_split w hw with hwE | htwE
  · exact h.EW (h.rho_nrm_E w hwE)
  · have h1 : rho * (t * w) * rho⁻¹ ∈ E := h.rho_nrm_E (t * w) htwE
    have h2 : rho * w * rho⁻¹ = t⁻¹ * (rho * (t * w) * rho⁻¹) := by
      rw [show rho * (t * w) * rho⁻¹ = (rho * t * rho⁻¹) * (rho * w * rho⁻¹) by group,
        h.rho_t]
      group
    rw [h2]
    exact W.mul_mem (W.inv_mem h.t_mem) (h.EW h1)

private theorem fzrAux_sq_coset [Finite G] (h : FzStr t tau lam rho Z E W Q R T) :
    ∀ y ∈ T, ∀ w ∈ W, (w * y) ^ 2 * (y ^ 2)⁻¹ ∈ E := by
  intro y hy w hw
  have htt : t * t = 1 := by rw [← pow_two]; exact h.t_sq
  have heq : (w * y) ^ 2 * (y ^ 2)⁻¹ = w * (y * w * y⁻¹) := by
    simp only [pow_two]; group
  rw [heq]
  rcases h.W_split w hw with hwE | htwE
  · exact E.mul_mem hwE (fzl_nrm_E h y hy w hwE)
  · obtain ⟨z, hzZ, hyt⟩ := h.T_t y hy
    obtain ⟨e, he, rfl⟩ : ∃ e ∈ E, w = t * e :=
      ⟨t * w, htwE, by rw [← mul_assoc, htt, one_mul]⟩
    have hte : t * e = e * t := h.W_comm t h.t_mem e (h.EW he)
    have hze : e * z = z * e := h.W_comm e (h.EW he) z (h.EW (h.ZE hzZ))
    have heq3 : t * e * (y * (t * e) * y⁻¹) = z * (e * (y * e * y⁻¹)) := by
      calc t * e * (y * (t * e) * y⁻¹)
          = t * e * (y * t * y⁻¹) * (y * e * y⁻¹) := by group
        _ = t * e * (t * z) * (y * e * y⁻¹) := by rw [hyt]
        _ = (t * e) * t * z * (y * e * y⁻¹) := by group
        _ = e * t * t * z * (y * e * y⁻¹) := by rw [hte]
        _ = e * (t * t) * z * (y * e * y⁻¹) := by group
        _ = e * z * (y * e * y⁻¹) := by rw [htt, mul_one]
        _ = z * e * (y * e * y⁻¹) := by rw [hze]
        _ = z * (e * (y * e * y⁻¹)) := by group
    rw [heq3]
    exact E.mul_mem (h.ZE hzZ) (E.mul_mem he (fzl_nrm_E h y hy e he))

private theorem fzrAux_sq_notin_E_of [Finite G] (h : FzStr t tau lam rho Z E W Q R T)
    {y w : G} (hy : y ∈ T) (hy2 : y ^ 2 ∉ E) (hw : w ∈ W) : (w * y) ^ 2 ∉ E := by
  intro hcon
  have hkey := fzrAux_sq_coset h y hy w hw
  have hinv : (y ^ 2)⁻¹ ∈ E := by
    have h' : (y ^ 2)⁻¹ = ((w * y) ^ 2)⁻¹ * ((w * y) ^ 2 * (y ^ 2)⁻¹) := by group
    rw [h']
    exact E.mul_mem (E.inv_mem hcon) hkey
  exact hy2 (by simpa using E.inv_mem hinv)

theorem fzr_x_sq_notin_E [Finite G] (h : FzStr t tau lam rho Z E W Q R T)
    (hP : t ∈ ⁅Q, zpowers rho⁆) : ∀ x ∈ Q, x ∉ W → x ^ 2 ∉ E := by
  obtain ⟨x0, hx0Q, hx0sq⟩ := fzr_x_exists_sq h hP
  have hx0W : x0 ∉ W := fun hx0W => hx0sq (fzrAux_sq_mem_E h x0 hx0W)
  have hcard : Nat.card Q = 4 * Nat.card W := by rw [h.card_Q, h.card_W]
  have hcos := fzc_sy3_rho_cosets h.WQ hcard
    (fun q hq w hw => h.nrm_W q (h.RT (h.QR hq)) w hw)
    (fun q hq => h.R_sq q (h.QR hq))
    (fun a ha b hb => h.R_comm a (h.QR ha) b (h.QR hb))
    h.rho_nrm_Q (fzrAux_rho_nrm_W h) h.rho_ord h.rho_QW hx0Q hx0W
  have hy1T : x0 ∈ T := h.RT (h.QR hx0Q)
  have hy2Q : rho * x0 * rho⁻¹ ∈ Q := h.rho_nrm_Q x0 hx0Q
  have hy2T : rho * x0 * rho⁻¹ ∈ T := h.RT (h.QR hy2Q)
  have hy2sq : (rho * x0 * rho⁻¹) ^ 2 ∉ E := by
    intro hmem
    rw [conj_pow] at hmem
    exact hx0sq (by
      have h' := fzrAux_rho_inv_nrm_E h (rho * x0 ^ 2 * rho⁻¹) hmem
      rwa [show rho⁻¹ * (rho * x0 ^ 2 * rho⁻¹) * rho = x0 ^ 2 by group] at h')
  have hy3Q : rho⁻¹ * x0 * rho ∈ Q := by
    have h2 : rho⁻¹ = rho ^ 2 := (fzrAux_rho_sq h).symm
    have h' := h.rho_nrm_Q (rho * x0 * rho⁻¹) hy2Q
    rw [show rho * (rho * x0 * rho⁻¹) * rho⁻¹ = rho ^ 2 * x0 * (rho ^ 2)⁻¹ by
      rw [pow_two]; group, ← h2] at h'
    simpa using h'
  have hy3T : rho⁻¹ * x0 * rho ∈ T := h.RT (h.QR hy3Q)
  have hy3sq : (rho⁻¹ * x0 * rho) ^ 2 ∉ E := by
    intro hmem
    have hsq : (rho⁻¹ * x0 * rho) ^ 2 = rho⁻¹ * x0 ^ 2 * rho := by
      simpa using conj_pow (a := rho⁻¹) (b := x0) (i := 2)
    rw [hsq] at hmem
    exact hx0sq (by
      have h' := h.rho_nrm_E (rho⁻¹ * x0 ^ 2 * rho) hmem
      rwa [show rho * (rho⁻¹ * x0 ^ 2 * rho) * rho⁻¹ = x0 ^ 2 by group] at h')
  intro x hxQ hxW
  rcases hcos x hxQ with hxW' | h1 | h2 | h3
  · exact absurd hxW' hxW
  · have hx_eq : x = (x * x0⁻¹) * x0 := by group
    rw [hx_eq]
    exact fzrAux_sq_notin_E_of h hy1T hx0sq h1
  · have hx_eq : x = (x * (rho * x0 * rho⁻¹)⁻¹) * (rho * x0 * rho⁻¹) := by group
    rw [hx_eq]
    exact fzrAux_sq_notin_E_of h hy2T hy2sq h2
  · have hx_eq : x = (x * (rho⁻¹ * x0 * rho)⁻¹) * (rho⁻¹ * x0 * rho) := by group
    rw [hx_eq]
    exact fzrAux_sq_notin_E_of h hy3T hy3sq h3

end CFSG.OddStandard.SmallF3.FritzII
