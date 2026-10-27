module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316C

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fzl_tau_sq {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) : tau ^ 2 = 1 := by
  rcases h.tau_sq with h1 | h1
  · exact h1
  · exfalso
    have hconj : ∀ q ∈ Q, t * q * t⁻¹ = q := by
      intro q hq
      have hw : ⁅tau, q⁆ ∈ W := h.tau_Q q hq
      have h1c : tau * q * tau⁻¹ = ⁅tau, q⁆ * q := by
        rw [commutatorElement_def]; group
      have h2c : tau * ⁅tau, q⁆ * tau⁻¹ = ⁅tau, q⁆⁻¹ := h.tau_W _ hw
      have h3c : tau ^ 2 * q * (tau ^ 2)⁻¹ = q := by
        calc tau ^ 2 * q * (tau ^ 2)⁻¹
            = tau * (tau * q * tau⁻¹) * tau⁻¹ := by
              simp only [pow_two]; group
          _ = tau * (⁅tau, q⁆ * q) * tau⁻¹ := by rw [h1c]
          _ = (tau * ⁅tau, q⁆ * tau⁻¹) * (tau * q * tau⁻¹) := by group
          _ = ⁅tau, q⁆⁻¹ * (⁅tau, q⁆ * q) := by rw [h2c, h1c]
          _ = q := by group
      rwa [h1] at h3c
    have hne : W ≠ Q := by
      intro heq
      have hc : Nat.card W = Nat.card Q := by rw [heq]
      rw [h.card_W, h.card_Q] at hc
      norm_num at hc
    obtain ⟨n, hnQ, hnW⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne h.WQ hne)
    refine h.Q_t n hnQ hnW ?_
    have hc : t * n * t⁻¹ = n := hconj n hnQ
    have hcomm : t * n = n * t := by
      calc t * n = (t * n * t⁻¹) * t := by group
        _ = n * t := by rw [hc]
    rw [← hcomm]; group

theorem fzl_Q_nrm_E {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) : ∀ n ∈ Q, ∀ e ∈ E, n * e * n⁻¹ ∈ E := by
  intro n hnQ e he
  by_cases hnW : n ∈ W
  · have hcomm : n * e = e * n := h.W_comm n hnW e (h.EW he)
    have heq : n * e * n⁻¹ = e := by
      calc n * e * n⁻¹ = (e * n) * n⁻¹ := by rw [hcomm]
        _ = e := by group
    rwa [heq]
  · have hnR : n ∈ R := h.QR hnQ
    have hnT : n ∈ T := h.RT hnR
    have hxW : n * e * n⁻¹ ∈ W := h.nrm_W n hnT e (h.EW he)
    rcases h.W_split (n * e * n⁻¹) hxW with hxE | htxE
    · exact hxE
    · exfalso
      set x : G := n * e * n⁻¹ with hxdef
      set e' : G := t * x with he'def
      have he'E : e' ∈ E := by rw [he'def]; exact htxE
      have hx_eq : x = t * e' := by
        rw [he'def]
        rw [← mul_assoc, ← pow_two, h.t_sq, one_mul]
      have hx2 : x ^ 2 = e ^ 2 := by
        have hz := h.R_Z n hnR (e ^ 2) (h.E_sq e he)
        calc x ^ 2 = n * e ^ 2 * n⁻¹ := by
              rw [hxdef]; simp only [pow_two]; group
          _ = e ^ 2 := hz
      have he'2 : e' ^ 2 = e ^ 2 := by
        have hcomm : Commute t e' := h.W_comm t h.t_mem e' (h.EW he'E)
        have hte'2 : (t * e') ^ 2 = e' ^ 2 := by
          rw [hcomm.mul_pow 2, h.t_sq, one_mul]
        rw [← hte'2, ← hx_eq, hx2]
      set z₁ : G := e' * e⁻¹ with hz1def
      have hz1E : z₁ ∈ E := E.mul_mem he'E (E.inv_mem he)
      have hz1_sq : z₁ ^ 2 = 1 := by
        have hcomm : Commute e' e := h.W_comm e' (h.EW he'E) e (h.EW he)
        rw [hz1def]
        rw [hcomm.inv_right.mul_pow 2, he'2]
        simp only [pow_two]; group
      have hz1Z : z₁ ∈ Z := h.E_invol z₁ hz1E hz1_sq
      have hz1W : z₁ ∈ W := h.EW hz1E
      have hz1eq : e' = z₁ * e := by rw [hz1def]; group
      have hne' : n * e' * n⁻¹ = t * e := by
        have hnz : n * z₁ * n⁻¹ = z₁ := h.R_Z n hnR z₁ hz1Z
        have hz1tz1 : z₁ * t * z₁ = t := by
          have hcomm : z₁ * t = t * z₁ := h.W_comm z₁ hz1W t h.t_mem
          calc z₁ * t * z₁ = (t * z₁) * z₁ := by rw [hcomm]
            _ = t * (z₁ * z₁) := by rw [mul_assoc]
            _ = t := by rw [← pow_two, hz1_sq, mul_one]
        calc n * e' * n⁻¹ = n * (z₁ * e) * n⁻¹ := by rw [hz1eq]
          _ = (n * z₁ * n⁻¹) * (n * e * n⁻¹) := by group
          _ = z₁ * (t * e') := by rw [hnz, ← hxdef, hx_eq]
          _ = z₁ * (t * (z₁ * e)) := by rw [hz1eq]
          _ = (z₁ * t * z₁) * e := by group
          _ = t * e := by rw [hz1tz1]
      obtain ⟨z, hzZ, hnzt⟩ := h.T_t n hnT
      have hz_ne : z ≠ 1 := by
        intro hz1
        exact h.Q_t n hnQ hnW (by rw [hnzt, hz1, mul_one])
      have hnx : n * x * n⁻¹ = z * e := by
        have htzt : t * z * t = z := by
          have hcomm : t * z = z * t := h.W_comm t h.t_mem z (h.EW (h.ZE hzZ))
          calc t * z * t = (z * t) * t := by rw [hcomm]
            _ = z * (t * t) := by rw [mul_assoc]
            _ = z := by rw [← pow_two, h.t_sq, mul_one]
        calc n * x * n⁻¹ = n * (t * e') * n⁻¹ := by rw [hx_eq]
          _ = (n * t * n⁻¹) * (n * e' * n⁻¹) := by group
          _ = (t * z) * (t * e) := by rw [hnzt, hne']
          _ = (t * z * t) * e := by group
          _ = z * e := by rw [htzt]
      have hn2W : n ^ 2 ∈ W := h.R_sq n hnR
      have hnxn : n * x * n⁻¹ = e := by
        have hcomm : n ^ 2 * e = e * n ^ 2 := h.W_comm (n ^ 2) hn2W e (h.EW he)
        calc n * x * n⁻¹ = n ^ 2 * e * (n ^ 2)⁻¹ := by
              rw [hxdef]; simp only [pow_two]; group
          _ = (e * n ^ 2) * (n ^ 2)⁻¹ := by rw [hcomm]
          _ = e := by simp only [pow_two]; group
      have hze : z * e = e := by rw [← hnx, hnxn]
      have hz1 : z = 1 := by
        have h := congrArg (· * e⁻¹) hze
        simpa [mul_assoc] using h
      exact hz_ne hz1

theorem fzl_nrm_E {t tau lam rho : G} {Z E W Q R T : Subgroup G}
    (h : FzStr t tau lam rho Z E W Q R T) : ∀ g ∈ T, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
  intro g hg e he
  rcases fzl_T_gen h g hg with hgQ | hgQ | hgQ | hgQ
  · exact fzl_Q_nrm_E h g hgQ e he
  · have hg_eq : g = tau * (tau⁻¹ * g) := by group
    have hqE : (tau⁻¹ * g) * e * (tau⁻¹ * g)⁻¹ ∈ E := fzl_Q_nrm_E h _ hgQ e he
    have hconj : tau * ((tau⁻¹ * g) * e * (tau⁻¹ * g)⁻¹) * tau⁻¹ ∈ E := by
      rw [h.tau_W _ (h.EW hqE)]
      exact E.inv_mem hqE
    have heq : g * e * g⁻¹ = tau * ((tau⁻¹ * g) * e * (tau⁻¹ * g)⁻¹) * tau⁻¹ := by
      rw [hg_eq]; group
    rwa [heq]
  · have hg_eq : g = lam * (lam⁻¹ * g) := by group
    have hqE : (lam⁻¹ * g) * e * (lam⁻¹ * g)⁻¹ ∈ E := fzl_Q_nrm_E h _ hgQ e he
    have heq : g * e * g⁻¹ = lam * ((lam⁻¹ * g) * e * (lam⁻¹ * g)⁻¹) * lam⁻¹ := by
      rw [hg_eq]; group
    rw [heq]
    exact h.lam_E.1 _ hqE
  · have hg_eq : g = (lam * tau) * ((lam * tau)⁻¹ * g) := by group
    have hqE : ((lam * tau)⁻¹ * g) * e * ((lam * tau)⁻¹ * g)⁻¹ ∈ E :=
      fzl_Q_nrm_E h _ hgQ e he
    have h1 : tau * (((lam * tau)⁻¹ * g) * e * ((lam * tau)⁻¹ * g)⁻¹) * tau⁻¹ ∈ E := by
      rw [h.tau_W _ (h.EW hqE)]
      exact E.inv_mem hqE
    have heq : g * e * g⁻¹
        = lam * (tau * (((lam * tau)⁻¹ * g) * e * ((lam * tau)⁻¹ * g)⁻¹) * tau⁻¹)
          * lam⁻¹ := by
      rw [hg_eq]; group
    rw [heq]
    exact h.lam_E.1 _ h1

end CFSG.OddStandard.SmallF3.FritzII
