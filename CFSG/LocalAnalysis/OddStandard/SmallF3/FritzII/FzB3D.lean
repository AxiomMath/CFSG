module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3C

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t q tau lam rho u : G} {Z E X W R T : Subgroup G}

theorem fzbs_tau_inv_q (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    tau * q * tau⁻¹ = q⁻¹ := by
  rcases hS.tau_q with hq | hqinv
  · exfalso
    obtain ⟨r, hr, hr_eq⟩ := hS.R_t_surj (u ^ 2) (hS.E_sq u hS.u_mem)
    set a : G := q⁻¹ * (r * q * r⁻¹) with ha_def
    have haX : a ∈ X := by simpa [ha_def] using (fzbs_aq hS hr).1
    have ha2 : a ^ 2 = t * (r * t * r⁻¹) := by simpa [ha_def] using (fzbs_aq hS hr).2
    have htt : t * t = 1 := by rw [← pow_two]; exact hS.t_sq
    have hrqr : r * q * r⁻¹ = q * a := by rw [ha_def]; group
    have hqtau : tau⁻¹ * q * tau = q := by
      have h := congrArg (fun x => tau⁻¹ * x * tau) hq
      have h2 : tau⁻¹ * (tau * q * tau⁻¹) * tau = q := by group
      rw [h2] at h
      exact h.symm
    have h1 : tau * r * tau⁻¹ * q * (tau * r * tau⁻¹)⁻¹ = q * a⁻¹ := by
      rw [show tau * r * tau⁻¹ * q * (tau * r * tau⁻¹)⁻¹ =
            tau * r * (tau⁻¹ * q * tau) * r⁻¹ * tau⁻¹ by group, hqtau,
          show tau * r * q * r⁻¹ * tau⁻¹ = tau * (r * q * r⁻¹) * tau⁻¹ by group, hrqr,
          show tau * (q * a) * tau⁻¹ = (tau * q * tau⁻¹) * (tau * a * tau⁻¹) by group,
          hq, hS.tau_X a haX]
    have h2 : tau * r * tau⁻¹ * q * (tau * r * tau⁻¹)⁻¹ = q * a := by
      have hw : ⁅r⁻¹, tau⁆ ∈ W := hS.R_comm r⁻¹ (inv_mem hr) tau hS.tau_R
      have hwdef : ⁅r⁻¹, tau⁆ = r⁻¹ * tau * r * tau⁻¹ := by
        rw [commutatorElement_def]; group
      have hr' : tau * r * tau⁻¹ = r * ⁅r⁻¹, tau⁆ := by rw [hwdef]; group
      rw [hr']
      have hwq : ⁅r⁻¹, tau⁆ * q * ⁅r⁻¹, tau⁆⁻¹ = q := by
        rw [hS.W_comm ⁅r⁻¹, tau⁆ hw q hS.q_mem]; group
      have e : r * ⁅r⁻¹, tau⁆ * q * (r * ⁅r⁻¹, tau⁆)⁻¹ =
          r * (⁅r⁻¹, tau⁆ * q * ⁅r⁻¹, tau⁆⁻¹) * r⁻¹ := by group
      rw [e, hwq, hrqr]
    have heq : q * a⁻¹ = q * a := h1.symm.trans h2
    have hainv : a⁻¹ = a := mul_left_cancel heq
    have ha2one : a ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [← hainv]
      exact mul_inv_cancel a
    have hu2 : u ^ 2 = 1 := by
      rw [← ha2one, ha2, hr_eq,
        show t * (t * u ^ 2) = u ^ 2 by rw [← mul_assoc, htt, one_mul]]
    exact hS.u_sq_ne hu2
  · exact hqinv

theorem fzbs_tau_W (hS : FzbsStr t q tau lam rho u Z E X W R T) {w : G} (hw : w ∈ W) :
    tau * w * tau⁻¹ = w⁻¹ := by
  rcases hS.W_split w hw with hx | hx
  · exact hS.tau_X w hx
  · have hqinv : tau * q⁻¹ * tau⁻¹ = q := by
      have h := fzbs_tau_inv_q hS
      calc tau * q⁻¹ * tau⁻¹ = (tau * q * tau⁻¹)⁻¹ := by group
        _ = (q⁻¹)⁻¹ := by rw [h]
        _ = q := by group
    have h1 : tau * (q * w) * tau⁻¹ = (q * w)⁻¹ := hS.tau_X (q * w) hx
    calc tau * w * tau⁻¹ = tau * (q⁻¹ * (q * w)) * tau⁻¹ := by group
      _ = (tau * q⁻¹ * tau⁻¹) * (tau * (q * w) * tau⁻¹) := by group
      _ = q * (q * w)⁻¹ := by rw [hqinv, h1]
      _ = w⁻¹ := by
            calc q * (q * w)⁻¹ = q * (w⁻¹ * q⁻¹) := by rw [mul_inv_rev]
              _ = (q * w⁻¹) * q⁻¹ := by group
              _ = (w⁻¹ * q) * q⁻¹ := by rw [hS.W_comm q hS.q_mem w⁻¹ (inv_mem hw)]
              _ = w⁻¹ := by group

theorem fzbs_tau_sq (hS : FzbsStr t q tau lam rho u Z E X W R T) : tau ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hS.tau_sq
  have htt : t * t = 1 := by rw [← pow_two]; exact hS.t_sq
  have ht2z : t ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hS.t_sq
  have htne : t ≠ 1 := fun h => hS.t_notin_E (by rw [h]; exact one_mem E)
  have hconj : tau * q ^ k * tau⁻¹ = q ^ (-k) := by
    rw [← conj_zpow (a := tau) (b := q) (i := k), fzbs_tau_inv_q hS, inv_zpow']
  have hfix : tau * q ^ k * tau⁻¹ = q ^ k := by
    rw [hk]; group
  have hk_eq : q ^ k = q ^ (-k) := hfix.symm.trans hconj
  have hprod : q ^ k * q ^ k = 1 := by
    nth_rewrite 1 [hk_eq]; rw [← zpow_add, neg_add_cancel, zpow_zero]
  have hq2k : q ^ (2 * k) = 1 := by
    rw [show (2 : ℤ) * k = k + k by ring, zpow_add]; exact hprod
  have htk : t ^ k = 1 := by
    rw [show t = q ^ (2 : ℤ) by rw [← hS.q_sq, zpow_ofNat], ← zpow_mul]; exact hq2k
  have hk_even : ∃ j : ℤ, k = 2 * j := by
    rcases Int.even_or_odd' k with ⟨j, hk | hk⟩
    · exact ⟨j, hk⟩
    · exfalso
      rw [hk, show t ^ (2 * j + 1) = t by
        rw [zpow_add, zpow_mul, ht2z, one_zpow, one_mul, zpow_one]] at htk
      exact htne htk
  obtain ⟨j, hj⟩ := hk_even
  have htau_j : tau ^ 2 = t ^ j := by
    rw [← hk, hj, zpow_mul]
    rw [show q ^ (2 : ℤ) = t by rw [zpow_ofNat]; exact hS.q_sq]
  have hexcl : tau ^ 2 ≠ t := by
    intro h2
    have hcent : ∀ x ∈ R, t * x = x * t := by
      intro x hx
      have hcW : ⁅tau, x⁆ ∈ W := hS.R_comm tau hS.tau_R x hx
      have htau_x : tau * x * tau⁻¹ = ⁅tau, x⁆ * x := conj_eq_commutatorElement_mul
      have h2' : tau * tau = t := by rw [← pow_two]; exact h2
      have hfix' : tau * tau * x * (tau * tau)⁻¹ = x := by
        calc tau * tau * x * (tau * tau)⁻¹ = tau * (tau * x * tau⁻¹) * tau⁻¹ := by group
          _ = tau * (⁅tau, x⁆ * x) * tau⁻¹ := by rw [htau_x]
          _ = (tau * ⁅tau, x⁆ * tau⁻¹) * (tau * x * tau⁻¹) := by group
          _ = (⁅tau, x⁆)⁻¹ * (⁅tau, x⁆ * x) := by rw [fzbs_tau_W hS hcW, htau_x]
          _ = x := by group
      rw [h2'] at hfix'
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x * t := by rw [hfix']
    obtain ⟨r0, hr0, hr0eq⟩ := hS.R_t_surj (u ^ 2) (hS.E_sq u hS.u_mem)
    have hb : t * (r0 * t * r0⁻¹) = 1 := by
      calc t * (r0 * t * r0⁻¹) = t * (t * r0 * r0⁻¹) := by rw [hcent r0 hr0]
        _ = (t * t) * (r0 * r0⁻¹) := by group
        _ = 1 := by rw [htt, one_mul, mul_inv_cancel]
    have hu2 : u ^ 2 = 1 := by
      calc u ^ 2 = t * (t * u ^ 2) := by rw [← mul_assoc, htt, one_mul]
        _ = t * (r0 * t * r0⁻¹) := by rw [hr0eq]
        _ = 1 := hb
    exact hS.u_sq_ne hu2
  have htau_eq : tau ^ 2 = 1 ∨ tau ^ 2 = t := by
    rcases Int.even_or_odd' j with ⟨i, hj | hj⟩
    · left
      rw [htau_j, hj, zpow_mul, ht2z, one_zpow]
    · right
      rw [htau_j, hj, zpow_add, zpow_mul, ht2z, one_zpow, one_mul, zpow_one]
  rcases htau_eq with h1 | h1
  · exact h1
  · exact absurd h1 hexcl

theorem fzbs_R_sq_X (hS : FzbsStr t q tau lam rho u Z E X W R T) {g : G} (hg : g ∈ R) :
    g ^ 2 ∈ X := by
  by_cases hX : g ^ 2 ∈ X
  · exact hX
  · have hg2W : g ^ 2 ∈ W := hS.R_sq g hg
    have hyX : q * g ^ 2 ∈ X := by
      rcases hS.W_split (g ^ 2) hg2W with h | h
      · exact absurd h hX
      · exact h
    set y : G := q * g ^ 2 with hy_def
    have hyW : y ∈ W := hS.XW hyX
    have hg2 : g ^ 2 = q⁻¹ * y := by rw [hy_def]; group
    set a : G := q⁻¹ * (g * q * g⁻¹) with ha_def
    have haX : a ∈ X := by simpa [ha_def] using (fzbs_aq hS hg).1
    have ha2 : a ^ 2 = t * (g * t * g⁻¹) := by simpa [ha_def] using (fzbs_aq hS hg).2
    have haW : a ∈ W := hS.XW haX
    have hgyX : g * y * g⁻¹ ∈ X := hS.R_X g hg y hyX
    have hgyW : g * y * g⁻¹ ∈ W := hS.XW hgyX
    have hgqinv : g * q⁻¹ * g⁻¹ = a⁻¹ * q⁻¹ := by
      have hgq : g * q * g⁻¹ = q * a := by rw [ha_def]; group
      rw [show g * q⁻¹ * g⁻¹ = (g * q * g⁻¹)⁻¹ by group, hgq]; group
    have hcomm : g * (q⁻¹ * y) * g⁻¹ = q⁻¹ * y := by
      rw [← hg2]; group
    have heq : a⁻¹ * q⁻¹ * (g * y * g⁻¹) = q⁻¹ * y := by
      have h1 : g * (q⁻¹ * y) * g⁻¹ = (g * q⁻¹ * g⁻¹) * (g * y * g⁻¹) := by group
      have h2 : a⁻¹ * q⁻¹ * (g * y * g⁻¹) = g * (q⁻¹ * y) * g⁻¹ := by rw [h1, hgqinv]
      rw [h2, hcomm]
    have hainvGY : a⁻¹ * (g * y * g⁻¹) = y := by
      have heq' : a⁻¹ * (g * y * g⁻¹) * q⁻¹ = y * q⁻¹ := by
        have e : a⁻¹ * (g * y * g⁻¹) * q⁻¹ = a⁻¹ * q⁻¹ * (g * y * g⁻¹) := by
          rw [show a⁻¹ * (g * y * g⁻¹) * q⁻¹ = a⁻¹ * ((g * y * g⁻¹) * q⁻¹) by group,
            hS.W_comm (g * y * g⁻¹) hgyW q⁻¹ (inv_mem hS.q_mem)]
          group
        rw [e, heq, hS.W_comm q⁻¹ (inv_mem hS.q_mem) y hyW]
      exact mul_right_cancel heq'
    have hGya : g * y * g⁻¹ = a * y := by
      calc g * y * g⁻¹ = a * (a⁻¹ * (g * y * g⁻¹)) := by group
        _ = a * y := by rw [hainvGY]
    have haZ : a ∈ Z := by
      have h := fzbs_comm_X hS hg hyX
      rw [hGya] at h
      rwa [show a * y * y⁻¹ = a by group] at h
    have hchi : t * (g * t * g⁻¹) = 1 := by
      rw [← ha2, hS.Z_sq a haZ]
    rcases (fzbs_chi_eq_one hS hg).mp hchi with hgW | hgtW
    · exact fzbs_W_sq_X hS hgW
    · set w : G := g * tau⁻¹ with hw_def
      have hwW : w ∈ W := by rwa [hw_def]
      have hg_eq : g = w * tau := by rw [hw_def]; group
      rw [hg_eq]
      have hsq : (w * tau) * (w * tau) = 1 := by
        rw [show (w * tau) * (w * tau) = (w * (tau * w * tau⁻¹)) * tau ^ 2 by group,
          fzbs_tau_W hS hwW, fzbs_tau_sq hS, mul_inv_cancel, one_mul]
      rw [pow_two, hsq]
      exact one_mem X

theorem fzbs_tau_comm_X (hS : FzbsStr t q tau lam rho u Z E X W R T) {r : G} (hr : r ∈ R) :
    ⁅tau, r⁆ ∈ X := by
  set s : G := rho * r * rho⁻¹ with hs_def
  set u_ : G := rho ^ 2 * r * (rho ^ 2)⁻¹ with hu_def
  have hsR : s ∈ R := by rw [hs_def]; exact hS.rho_R r hr
  have huR : u_ ∈ R := by
    have h : rho * (rho * r * rho⁻¹) * rho⁻¹ ∈ R := by
      simpa [hs_def] using hS.rho_R s hsR
    rw [hu_def, show rho ^ 2 * r * (rho ^ 2)⁻¹ = rho * (rho * r * rho⁻¹) * rho⁻¹ by
      rw [sq]; group]
    exact h
  have hA : ∀ x y : G, ⁅tau, x * y⁆ = ⁅tau, x⁆ * (x * ⁅tau, y⁆ * x⁻¹) := by
    intro x y; group
  have hB : ∀ x : G, x ∈ R → ∀ c ∈ W, x * c * x⁻¹ ∈ X ↔ c ∈ X := by
    intro x hx c hc
    have hw : x * c * x⁻¹ * c⁻¹ ∈ X := fzbs_R_W_X hS hx hc
    have h := fzbs_W_X_mul hS (hS.XW hw) hc
    rw [show (x * c * x⁻¹ * c⁻¹) * c = x * c * x⁻¹ by group] at h
    simpa [hw] using h
  have hC : ∀ x y : G, x ∈ R → y ∈ R →
      (⁅tau, x * y⁆ ∈ X ↔ (⁅tau, x⁆ ∈ X ↔ ⁅tau, y⁆ ∈ X)) := by
    intro x y hx hy
    have hcxW : ⁅tau, x⁆ ∈ W := hS.R_comm tau hS.tau_R x hx
    have hcyW : ⁅tau, y⁆ ∈ W := hS.R_comm tau hS.tau_R y hy
    have hxyW : x * ⁅tau, y⁆ * x⁻¹ ∈ W := hS.R_W x hx _ hcyW
    calc ⁅tau, x * y⁆ ∈ X ↔ ⁅tau, x⁆ * (x * ⁅tau, y⁆ * x⁻¹) ∈ X := by rw [hA x y]
      _ ↔ (⁅tau, x⁆ ∈ X ↔ x * ⁅tau, y⁆ * x⁻¹ ∈ X) :=
            fzbs_W_X_mul hS hcxW hxyW
      _ ↔ (⁅tau, x⁆ ∈ X ↔ ⁅tau, y⁆ ∈ X) :=
            iff_congr Iff.rfl (hB x hx ⁅tau, y⁆ hcyW)
  have hD1gen : ∀ g : G, g * tau = tau * g →
      ⁅tau, g * r * g⁻¹⁆ = g * ⁅tau, r⁆ * g⁻¹ := by
    intro g hg
    have hginv : g⁻¹ * tau⁻¹ = tau⁻¹ * g⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hg]
    calc tau * (g * r * g⁻¹) * tau⁻¹ * (g * r * g⁻¹)⁻¹
        = (tau * g) * r * (g⁻¹ * tau⁻¹) * (g * r⁻¹ * g⁻¹) := by group
      _ = (g * tau) * r * (tau⁻¹ * g⁻¹) * (g * r⁻¹ * g⁻¹) := by rw [← hg, hginv]
      _ = g * (tau * r * tau⁻¹ * r⁻¹) * g⁻¹ := by group
  have hD1 : ⁅tau, s⁆ = rho * ⁅tau, r⁆ * rho⁻¹ := by
    simpa [hs_def] using hD1gen rho hS.tau_rho.symm
  have hrho2tau : rho ^ 2 * tau = tau * rho ^ 2 := by
    rw [show rho ^ 2 * tau = rho * (rho * tau) by rw [sq]; group, ← hS.tau_rho,
        show rho * (tau * rho) = (rho * tau) * rho by group, ← hS.tau_rho,
        show (tau * rho) * rho = tau * rho ^ 2 by rw [sq]; group]
  have hrho2t : rho ^ 2 * t * (rho ^ 2)⁻¹ = t := by
    rw [show rho ^ 2 * t * (rho ^ 2)⁻¹ = rho * (rho * t * rho⁻¹) * rho⁻¹ by
      rw [sq]; group, hS.rho_t, hS.rho_t]
  have hD1_2 : ⁅tau, u_⁆ = rho ^ 2 * ⁅tau, r⁆ * (rho ^ 2)⁻¹ := by
    simpa [hu_def] using hD1gen (rho ^ 2) hrho2tau
  have hDX : ∀ c ∈ W, rho * c * rho⁻¹ ∈ X ↔ c ∈ X := by
    intro c hc
    refine ⟨fun h => ?_, fun h => hS.rho_X c h⟩
    have h' := fzbs_zpow_conj hS.rho_cube hS.rho_X
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers rho)) h
    rwa [show rho⁻¹ * (rho * c * rho⁻¹) * (rho⁻¹)⁻¹ = c by group] at h'
  have hDX2 : ∀ c ∈ W, rho ^ 2 * c * (rho ^ 2)⁻¹ ∈ X ↔ c ∈ X := by
    intro c hc
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' := fzbs_zpow_conj hS.rho_cube hS.rho_X
        (Subgroup.inv_mem _
          (Subgroup.pow_mem (K := zpowers rho) (Subgroup.mem_zpowers rho) 2)) h
      rwa [show (rho ^ 2)⁻¹ * (rho ^ 2 * c * (rho ^ 2)⁻¹) * ((rho ^ 2)⁻¹)⁻¹ = c by
        group] at h'
    · have h2 : rho * (rho * c * rho⁻¹) * rho⁻¹ ∈ X := hS.rho_X (rho * c * rho⁻¹)
        (hS.rho_X c h)
      have heq : rho ^ 2 * c * (rho ^ 2)⁻¹ = rho * (rho * c * rho⁻¹) * rho⁻¹ := by
        rw [sq]; group
      rwa [heq]
  have hE : ∀ w ∈ W, ⁅tau, w⁆ ∈ X := by
    intro w hw
    have hw2 : w * w ∈ X := by simpa [pow_two] using fzbs_W_sq_X hS hw
    have h1 : ⁅tau, w⁆ = (w * w)⁻¹ := by
      rw [commutatorElement_def, fzbs_tau_W hS hw]
      exact (mul_inv_rev w w).symm
    rw [h1]
    exact inv_mem hw2
  have hEtau : ∀ w ∈ W, ⁅tau, w * tau⁆ ∈ X := by
    intro w hw
    have h1 : ⁅tau, w * tau⁆ = ⁅tau, w⁆ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [h1]
    exact hE w hw
  have hN_R : r * s * u_ ∈ R := mul_mem (mul_mem hr hsR) huR
  have hchi : t * ((r * s * u_) * t * (r * s * u_)⁻¹) = 1 := by
    have h1 := fzbs_chi_mul hS (mul_mem hr hsR) huR
    have h2 := fzbs_chi_mul hS hr hsR
    have h3 : t * (s * t * s⁻¹) = rho * (t * (r * t * r⁻¹)) * rho⁻¹ := by
      simpa [hs_def] using fzbs_chi_conj (g := rho) (r := r) hS.rho_t
    have h4 : t * (u_ * t * u_⁻¹) = rho ^ 2 * (t * (r * t * r⁻¹)) * (rho ^ 2)⁻¹ := by
      simpa [hu_def] using fzbs_chi_conj (g := rho ^ 2) (r := r) hrho2t
    rw [h1, h2, h3, h4]
    exact fzbs_Z_norm hS (hS.R_t r hr)
  have hNW : r * s * u_ ∈ W ∨ (r * s * u_) * tau⁻¹ ∈ W :=
    (fzbs_chi_eq_one hS hN_R).mp hchi
  have hcN_X : ⁅tau, r * s * u_⁆ ∈ X := by
    rcases hNW with hNW | hNW
    · have hw2 : (r * s * u_) * (r * s * u_) ∈ X := by
        simpa [pow_two] using fzbs_W_sq_X hS hNW
      have h1 : ⁅tau, r * s * u_⁆ = ((r * s * u_) * (r * s * u_))⁻¹ := by
        rw [commutatorElement_def, fzbs_tau_W hS hNW]
        exact (mul_inv_rev (r * s * u_) (r * s * u_)).symm
      rw [h1]
      exact inv_mem hw2
    · set w : G := (r * s * u_) * tau⁻¹ with hw_def
      have hcw : ⁅tau, w⁆ ∈ X := by
        have hw2 : w * w ∈ X := by simpa [pow_two] using fzbs_W_sq_X hS hNW
        have h1 : ⁅tau, w⁆ = (w * w)⁻¹ := by
          rw [hw_def, commutatorElement_def, fzbs_tau_W hS hNW]
          exact (mul_inv_rev (r * s * u_ * tau⁻¹) (r * s * u_ * tau⁻¹)).symm
        rw [h1]
        exact inv_mem hw2
      have hNw : r * s * u_ = w * tau := by rw [hw_def]; group
      have h2 : ⁅tau, r * s * u_⁆ = ⁅tau, w⁆ := by
        rw [hNw, commutatorElement_def, commutatorElement_def]; group
      rwa [h2]
  have hcrW : ⁅tau, r⁆ ∈ W := hS.R_comm tau hS.tau_R r hr
  have hcs_iff : ⁅tau, s⁆ ∈ X ↔ ⁅tau, r⁆ ∈ X := by
    rw [hD1]; exact hDX ⁅tau, r⁆ hcrW
  have hcu_iff : ⁅tau, u_⁆ ∈ X ↔ ⁅tau, r⁆ ∈ X := by
    rw [hD1_2]; exact hDX2 ⁅tau, r⁆ hcrW
  have key : ⁅tau, r * s * u_⁆ ∈ X ↔ ⁅tau, r⁆ ∈ X := by
    calc ⁅tau, r * s * u_⁆ ∈ X ↔ (⁅tau, r * s⁆ ∈ X ↔ ⁅tau, u_⁆ ∈ X) :=
          hC (r * s) u_ (mul_mem hr hsR) huR
      _ ↔ ((⁅tau, r⁆ ∈ X ↔ ⁅tau, s⁆ ∈ X) ↔ ⁅tau, u_⁆ ∈ X) :=
            iff_congr (hC r s hr hsR) Iff.rfl
      _ ↔ ((⁅tau, r⁆ ∈ X ↔ ⁅tau, r⁆ ∈ X) ↔ ⁅tau, r⁆ ∈ X) :=
            iff_congr (iff_congr Iff.rfl hcs_iff) hcu_iff
      _ ↔ ⁅tau, r⁆ ∈ X := by tauto
  exact key.mp hcN_X

end CFSG.OddStandard.SmallF3.FritzII
