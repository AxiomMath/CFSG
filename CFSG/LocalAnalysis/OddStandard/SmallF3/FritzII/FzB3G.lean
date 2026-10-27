module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3F

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t q tau lam rho u : G} {Z E X W R T : Subgroup G}

private lemma fzbs_3g_u4 (hS : FzbsStr t q tau lam rho u Z E X W R T) : u ^ (4 : ℕ) = 1 := by
  have h : (u ^ 2) ^ 2 = 1 := hS.Z_sq (u ^ 2) (hS.E_sq u hS.u_mem)
  simpa [show (u ^ 2) ^ 2 = u ^ 4 by group] using h

private lemma fzbs_3g_u2sq (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    u ^ 2 * u ^ 2 = 1 := by
  rw [← pow_two]
  exact hS.Z_sq (u ^ 2) (hS.E_sq u hS.u_mem)

private lemma fzbs_3g_u2_inv (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    (u ^ 2)⁻¹ = u ^ 2 := inv_eq_of_mul_eq_one_right (fzbs_3g_u2sq hS)

private lemma fzbs_3g_u3_mul (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    u ^ 3 * u ^ 3 = u ^ 2 := by
  rw [← pow_add, show (3 : ℕ) + 3 = 4 + 2 by norm_num, pow_add, fzbs_3g_u4 hS, one_mul]

private lemma fzbs_3g_tt (hS : FzbsStr t q tau lam rho u Z E X W R T) : t * t = 1 := by
  rw [← pow_two]; exact hS.t_sq

private lemma fzbs_3g_u2_mul_u2 (hS : FzbsStr t q tau lam rho u Z E X W R T) (x : G) :
    u ^ 2 * (u ^ 2 * x) = x := by
  rw [← mul_assoc, fzbs_3g_u2sq hS, one_mul]

private lemma fzbs_3g_mul_u2sq (hS : FzbsStr t q tau lam rho u Z E X W R T) (x : G) :
    x * u ^ 2 * u ^ 2 = x := by
  rw [mul_assoc, fzbs_3g_u2sq hS, mul_one]

private lemma fzbs_3g_zpowers_u_cases (hS : FzbsStr t q tau lam rho u Z E X W R T) {x : G}
    (hx : x ∈ zpowers u) : x = 1 ∨ x = u ∨ x = u ^ 2 ∨ x = u ^ 3 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h4 : u ^ (4 : ℤ) = 1 := by rw [zpow_ofNat]; exact fzbs_3g_u4 hS
  rw [← Int.emod_add_mul_ediv k 4, zpow_add, zpow_mul, h4, one_zpow, mul_one]
  have h0 := Int.emod_nonneg k (show (4 : ℤ) ≠ 0 by norm_num)
  have hlt := Int.emod_lt_of_pos k (show (0 : ℤ) < 4 by norm_num)
  interval_cases (k % 4) <;> simp [zpow_ofNat]

private lemma fzbs_3g_sq_eq_one (hS : FzbsStr t q tau lam rho u Z E X W R T) {x : G}
    (hx : x ∈ zpowers u) (hx2 : x ^ 2 = 1) : x = 1 ∨ x = u ^ 2 := by
  rcases fzbs_3g_zpowers_u_cases hS hx with h | h | h | h
  · exact Or.inl h
  · exfalso; rw [h] at hx2; exact hS.u_sq_ne hx2
  · exact Or.inr h
  · exfalso
    rw [h] at hx2
    have h3 : (u ^ 3) ^ 2 = u ^ 2 := by rw [pow_two (u ^ 3)]; exact fzbs_3g_u3_mul hS
    rw [h3] at hx2
    exact hS.u_sq_ne hx2

private lemma fzbs_3g_conj_eq_of_comm_one {a b : G} (h : ⁅a, b⁆ = 1) :
    a * b * a⁻¹ = b :=
  mul_inv_eq_one.mp h

private lemma fzbs_3g_comm_r_mul_u (hS : FzbsStr t q tau lam rho u Z E X W R T) {r s : G}
    (hrR : r ∈ R) (hs : s = tau ∨ s = q * tau) : ⁅s, r * u⁆ = ⁅s, r⁆ * u ^ 2 := by
  have huX : u ∈ X := hS.EX hS.u_mem
  have huW : u ∈ W := hS.XW huX
  have hs_u : s * u * s⁻¹ = u⁻¹ := by
    rcases hs with rfl | rfl
    · exact hS.tau_X u huX
    · rw [show q * tau * u * (q * tau)⁻¹ = q * (tau * u * tau⁻¹) * q⁻¹ by group,
        hS.tau_X u huX]
      rw [show q * u⁻¹ * q⁻¹ = u⁻¹ by
        rw [hS.W_comm q hS.q_mem u⁻¹ (Subgroup.inv_mem _ huW)]; group]
  rw [commutatorElement_def]
  rw [show s * (r * u) * s⁻¹ * (r * u)⁻¹
      = (s * r * s⁻¹ * r⁻¹) * (r * (s * u * s⁻¹ * u⁻¹) * r⁻¹) by group]
  rw [hs_u, show u⁻¹ * u⁻¹ = u ^ 2 by rw [← mul_inv_rev, ← pow_two, fzbs_3g_u2_inv hS],
    hS.R_Z r hrR (u ^ 2) (hS.E_sq u hS.u_mem), commutatorElement_def]

theorem fzbs_r_lam (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    ∃ r ∈ ⁅R, zpowers rho⁆, r * t * r⁻¹ = t * u ^ 2 ∧ lam * r * lam⁻¹ = r := by
  obtain ⟨r, hrP, hr⟩ := fzbs_P_chi_surj hS (hS.E_sq u hS.u_mem)
  have hrR : r ∈ R := fzbs_P_le_R hS hrP
  have hu2Z : u ^ 2 ∈ Z := hS.E_sq u hS.u_mem
  let r' := lam * r * lam⁻¹
  have hr'P : r' ∈ ⁅R, zpowers rho⁆ := by
    show lam * r * lam⁻¹ ∈ _
    exact fzbs_P_lam hS hrP
  have htlam : lam * (t * u ^ 2) * lam⁻¹ = t * u ^ 2 := by
    rw [← conj_mul, hS.lam_t, ← conj_pow, hS.u_lam]
  have hr't : r' * t * r'⁻¹ = t * u ^ 2 := by
    have h := fzbs_chi_conj (g := lam) (r := r) hS.lam_t
    rw [hr, show t * (t * u ^ 2) = u ^ 2 by rw [← mul_assoc, fzbs_3g_tt hS, one_mul],
      show lam * u ^ 2 * lam⁻¹ = u ^ 2 by rw [← conj_pow, hS.u_lam]] at h
    have htu : t * (t * u ^ 2) = u ^ 2 := by rw [← mul_assoc, fzbs_3g_tt hS, one_mul]
    rw [← htu] at h
    exact mul_left_cancel h
  let m := r⁻¹ * r'
  have hmP : m ∈ ⁅R, zpowers rho⁆ := by
    show r⁻¹ * (lam * r * lam⁻¹) ∈ _
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hrP) hr'P
  have hRZinv : r⁻¹ * u ^ 2 * r = u ^ 2 := by
    simpa using hS.R_Z r⁻¹ (Subgroup.inv_mem _ hrR) (u ^ 2) hu2Z
  have hmt : m * t * m⁻¹ = t := by
    show (r⁻¹ * (lam * r * lam⁻¹)) * t * (r⁻¹ * (lam * r * lam⁻¹))⁻¹ = t
    have hr_inv_t : r⁻¹ * t * r = t * u ^ 2 := by
      have h1 : t = (r⁻¹ * t * r) * u ^ 2 := by
        calc t = r⁻¹ * (r * t * r⁻¹) * r := by group
          _ = r⁻¹ * (t * u ^ 2) * r := by rw [hr]
          _ = (r⁻¹ * t * r) * (r⁻¹ * u ^ 2 * r) := by group
          _ = (r⁻¹ * t * r) * u ^ 2 := by rw [hRZinv]
      calc r⁻¹ * t * r = ((r⁻¹ * t * r) * u ^ 2) * u ^ 2 :=
            (fzbs_3g_mul_u2sq hS (r⁻¹ * t * r)).symm
        _ = t * u ^ 2 := by rw [← h1]
    calc (r⁻¹ * (lam * r * lam⁻¹)) * t * (r⁻¹ * (lam * r * lam⁻¹))⁻¹
        = r⁻¹ * ((lam * r * lam⁻¹) * t * (lam * r * lam⁻¹)⁻¹) * r := by group
      _ = r⁻¹ * (t * u ^ 2) * r := by rw [hr't]
      _ = (r⁻¹ * t * r) * (r⁻¹ * u ^ 2 * r) := by group
      _ = (t * u ^ 2) * u ^ 2 := by rw [hr_inv_t, hRZinv]
      _ = t := fzbs_3g_mul_u2sq hS t
  have hmX : m ∈ X := fzbs_P_ker hS hmP hmt
  have hmlam : lam * m * lam⁻¹ = m⁻¹ := by
    show lam * (r⁻¹ * (lam * r * lam⁻¹)) * lam⁻¹ = (r⁻¹ * (lam * r * lam⁻¹))⁻¹
    have hr'lam : lam * (lam * r * lam⁻¹) * lam⁻¹ = r := by
      calc lam * (lam * r * lam⁻¹) * lam⁻¹ = (lam * lam) * r * (lam⁻¹ * lam⁻¹) := by
            group
        _ = lam ^ 2 * r * (lam⁻¹) ^ 2 := by rw [← pow_two, ← pow_two]
        _ = r := by
              rw [hS.lam_sq, show (lam⁻¹) ^ 2 = 1 by rw [inv_pow, hS.lam_sq, inv_one]]
              group
    rw [show lam * (r⁻¹ * (lam * r * lam⁻¹)) * lam⁻¹
          = (lam * r * lam⁻¹)⁻¹ * (lam * (lam * r * lam⁻¹) * lam⁻¹) by group,
      hr'lam]
    group
  obtain ⟨e, heE, heq | heq⟩ := hS.lam_X_inv m hmX hmlam
  · have heW : e ∈ W := hS.XW (hS.EX heE)
    have het : e * t * e⁻¹ = t := by rw [hS.W_comm e heW t (hS.XW hS.t_mem)]; group
    have hmeq : lam * r * lam⁻¹ = r * (e * (lam * e * lam⁻¹)⁻¹) := by
      have h1 : r * m = r * (e * (lam * e * lam⁻¹)⁻¹) := by rw [heq]
      have h2 : r * m = lam * r * lam⁻¹ := by
        show r * (r⁻¹ * (lam * r * lam⁻¹)) = lam * r * lam⁻¹
        group
      rw [← h2]; exact h1
    refine ⟨r * e, Subgroup.mul_mem _ hrP (fzbs_E_le_P hS heE), ?_, ?_⟩
    · rw [show r * e * t * (r * e)⁻¹ = r * (e * t * e⁻¹) * r⁻¹ by group, het]
      exact hr
    · rw [show lam * (r * e) * lam⁻¹
          = (lam * r * lam⁻¹) * (lam * e * lam⁻¹) by group, hmeq]
      group
  · exfalso
    have heW : e ∈ W := hS.XW (hS.EX heE)
    have heit : e⁻¹ * t * e = t := by
      rw [hS.W_comm e⁻¹ (Subgroup.inv_mem _ heW) t (hS.XW hS.t_mem)]; group
    have hmeq : lam * r * lam⁻¹ = r * (t * (e * (lam * e * lam⁻¹)⁻¹)) := by
      have h1 : r * m = r * (t * (e * (lam * e * lam⁻¹)⁻¹)) := by rw [heq]
      have h2 : r * m = lam * r * lam⁻¹ := by
        show r * (r⁻¹ * (lam * r * lam⁻¹)) = lam * r * lam⁻¹
        group
      rw [← h2]; exact h1
    have hr0lam : lam * (r * e) * lam⁻¹ = r * t * e := by
      rw [show lam * (r * e) * lam⁻¹
          = (lam * r * lam⁻¹) * (lam * e * lam⁻¹) by group, hmeq]
      group
    have hgoal : (r * e)⁻¹ * lam * (r * e) = t * lam := by
      rw [show (r * e)⁻¹ * lam * (r * e)
          = (r * e)⁻¹ * (lam * (r * e) * lam⁻¹) * lam by group, hr0lam]
      rw [show (r * e)⁻¹ * (r * t * e) = e⁻¹ * t * e by group, heit]
    exact hS.lam_not_conj (r * e)⁻¹ (by simpa using hgoal)

theorem fzbs_r3 (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    ∃ s r₃ : G, (s = tau ∨ s = q * tau) ∧ r₃ ∈ ⁅R, zpowers rho⁆ ∧
      r₃ * t * r₃⁻¹ = t * u ^ 2 ∧ lam * r₃ * lam⁻¹ = r₃ ∧ s * r₃ * s⁻¹ = r₃ := by
  obtain ⟨r, hrP, hrt, hrl⟩ := fzbs_r_lam hS
  have hrR : r ∈ R := fzbs_P_le_R hS hrP
  let c := ⁅tau, r⁆
  let a := q⁻¹ * (r * q * r⁻¹)
  have hcE : c ∈ E := fzbs_P_tau hS hrP
  have hcW : c ∈ W := hS.XW (hS.EX hcE)
  have haE : a ∈ E := fzbs_P_aq hS hrP
  have haW : a ∈ W := hS.XW (hS.EX haE)
  have huW : u ∈ W := hS.XW (hS.EX hS.u_mem)
  have htW : t ∈ W := hS.XW hS.t_mem
  have hruP : r * u ∈ ⁅R, zpowers rho⁆ :=
    Subgroup.mul_mem _ hrP (fzbs_E_le_P hS hS.u_mem)
  have hut : u * t * u⁻¹ = t := by rw [hS.W_comm u huW t htW]; group
  have hru_t : r * u * t * (r * u)⁻¹ = t * u ^ 2 := by
    rw [show r * u * t * (r * u)⁻¹ = r * (u * t * u⁻¹) * r⁻¹ by group, hut]
    exact hrt
  have hru_lam : lam * (r * u) * lam⁻¹ = r * u := by
    rw [show lam * (r * u) * lam⁻¹ = (lam * r * lam⁻¹) * (lam * u * lam⁻¹) by group,
      hrl, hS.u_lam]
  have hcq : q * c * q⁻¹ = c := by rw [hS.W_comm q hS.q_mem c hcW]; group
  have htau_r : tau * r * tau⁻¹ = c * r := by
    show tau * r * tau⁻¹ = ⁅tau, r⁆ * r
    rw [commutatorElement_def]; group
  have hqr_inv : q * r * q⁻¹ * r⁻¹ = a⁻¹ := by
    show q * r * q⁻¹ * r⁻¹ = (q⁻¹ * (r * q * r⁻¹))⁻¹
    have h1 : r * q * r⁻¹ = q * a := by
      show r * q * r⁻¹ = q * (q⁻¹ * (r * q * r⁻¹)); group
    calc q * r * q⁻¹ * r⁻¹ = q * (r * q * r⁻¹)⁻¹ := by group
      _ = q * (q * a)⁻¹ := by rw [h1]
      _ = q * (a⁻¹ * q⁻¹) := by rw [mul_inv_rev]
      _ = a⁻¹ := by
            rw [show q * (a⁻¹ * q⁻¹) = q * a⁻¹ * q⁻¹ by group,
              hS.W_comm q hS.q_mem a⁻¹ (Subgroup.inv_mem _ haW)]
            group
  have hqtau : ⁅q * tau, r⁆ = c * a⁻¹ := by
    rw [commutatorElement_def]
    calc q * tau * r * (q * tau)⁻¹ * r⁻¹
        = q * (tau * r * tau⁻¹) * q⁻¹ * r⁻¹ := by group
      _ = q * (c * r) * q⁻¹ * r⁻¹ := by rw [htau_r]
      _ = (q * c * q⁻¹) * (q * r * q⁻¹ * r⁻¹) := by group
      _ = c * (q * r * q⁻¹ * r⁻¹) := by rw [hcq]
      _ = c * a⁻¹ := by rw [hqr_inv]
  have hlam_tau : lam * tau * lam⁻¹ = tau := by rw [← hS.tau_lam]; group
  have hc_lam : lam * c * lam⁻¹ = c := by
    show lam * ⁅tau, r⁆ * lam⁻¹ = ⁅tau, r⁆
    rw [commutatorElement_def]
    rw [show lam * (tau * r * tau⁻¹ * r⁻¹) * lam⁻¹
        = (lam * tau * lam⁻¹) * (lam * r * lam⁻¹) * (lam * tau * lam⁻¹)⁻¹
          * (lam * r * lam⁻¹)⁻¹ by group, hlam_tau, hrl]
  have hcu : c ∈ zpowers u := hS.lam_E_fix c hcE hc_lam
  have ha_lam : lam * a * lam⁻¹ = a := by
    show lam * (q⁻¹ * (r * q * r⁻¹)) * lam⁻¹ = q⁻¹ * (r * q * r⁻¹)
    rw [show lam * (q⁻¹ * (r * q * r⁻¹)) * lam⁻¹
        = (lam * q * lam⁻¹)⁻¹ * ((lam * r * lam⁻¹) * (lam * q * lam⁻¹)
          * (lam * r * lam⁻¹)⁻¹) by group, hS.lam_q, hrl]
  have hau : a ∈ zpowers u := hS.lam_E_fix a haE ha_lam
  have ha2 : a ^ 2 = u ^ 2 := by
    have h : a ^ 2 = t * (r * t * r⁻¹) := (fzbs_aq hS hrR).2
    rw [hrt] at h
    simpa [show t * (t * u ^ 2) = u ^ 2 by rw [← mul_assoc, fzbs_3g_tt hS, one_mul]] using h
  have step : c ^ 2 = u ^ 2 → ∃ s r₃ : G, (s = tau ∨ s = q * tau) ∧
      r₃ ∈ ⁅R, zpowers rho⁆ ∧ r₃ * t * r₃⁻¹ = t * u ^ 2 ∧
      lam * r₃ * lam⁻¹ = r₃ ∧ s * r₃ * s⁻¹ = r₃ := by
    intro hc2
    have hainv2 : (a⁻¹) ^ 2 = u ^ 2 := by rw [inv_pow, ha2, fzbs_3g_u2_inv hS]
    have hca : Commute c a⁻¹ := hS.W_comm c hcW a⁻¹ (Subgroup.inv_mem _ haW)
    have hw2 : (c * a⁻¹) ^ 2 = 1 := by rw [hca.mul_pow 2, hc2, hainv2, fzbs_3g_u2sq hS]
    have hwu : c * a⁻¹ ∈ zpowers u := Subgroup.mul_mem _ hcu (Subgroup.inv_mem _ hau)
    rcases fzbs_3g_sq_eq_one hS hwu hw2 with hw | hw
    · exact ⟨q * tau, r, Or.inr rfl, hrP, hrt, hrl,
        fzbs_3g_conj_eq_of_comm_one (show ⁅q * tau, r⁆ = 1 by rw [hqtau, hw])⟩
    · exact ⟨q * tau, r * u, Or.inr rfl, hruP, hru_t, hru_lam,
        fzbs_3g_conj_eq_of_comm_one (show ⁅q * tau, r * u⁆ = 1 by
          rw [fzbs_3g_comm_r_mul_u hS hrR (Or.inr rfl), hqtau, hw, fzbs_3g_u2sq hS])⟩
  rcases fzbs_3g_zpowers_u_cases hS hcu with hc | hc | hc | hc
  · exact ⟨tau, r, Or.inl rfl, hrP, hrt, hrl,
      fzbs_3g_conj_eq_of_comm_one (show ⁅tau, r⁆ = 1 from hc)⟩
  · exact step (by rw [hc])
  · exact ⟨tau, r * u, Or.inl rfl, hruP, hru_t, hru_lam,
      fzbs_3g_conj_eq_of_comm_one (show ⁅tau, r * u⁆ = 1 by
        rw [fzbs_3g_comm_r_mul_u hS hrR (Or.inl rfl), show ⁅tau, r⁆ = u ^ 2 from hc,
          fzbs_3g_u2sq hS])⟩
  · exact step (by rw [hc, pow_two (u ^ 3)]; exact fzbs_3g_u3_mul hS)

theorem fzbs_r3_sq (hS : FzbsStr t q tau lam rho u Z E X W R T) {s r₃ : G}
    (hs : s = tau ∨ s = q * tau) (hr₃ : r₃ ∈ ⁅R, zpowers rho⁆)
    (hr₃t : r₃ * t * r₃⁻¹ = t * u ^ 2) (hr₃l : lam * r₃ * lam⁻¹ = r₃)
    (hr₃s : s * r₃ * s⁻¹ = r₃) : r₃ ^ 2 ∈ E := by
  have hr₃R : r₃ ∈ R := fzbs_P_le_R hS hr₃
  have hr₃sqX : r₃ ^ 2 ∈ X := fzbs_R_sq_X hS hr₃R
  rcases hS.X_split (r₃ ^ 2) hr₃sqX with hE | hE
  · exact hE
  · exfalso
    let e₃ := t * r₃ ^ 2
    have he₃E : e₃ ∈ E := by show t * r₃ ^ 2 ∈ E; exact hE
    have hr₃sq : r₃ ^ 2 = t * e₃ := by
      show r₃ ^ 2 = t * (t * r₃ ^ 2); rw [← mul_assoc, fzbs_3g_tt hS, one_mul]
    have he₃_lam : lam * e₃ * lam⁻¹ = e₃ := by
      show lam * (t * r₃ ^ 2) * lam⁻¹ = t * r₃ ^ 2
      rw [show lam * (t * r₃ ^ 2) * lam⁻¹
          = (lam * t * lam⁻¹) * (lam * r₃ * lam⁻¹) ^ 2 by rw [conj_pow, conj_mul],
        hS.lam_t, hr₃l]
    have he₃u : e₃ ∈ zpowers u := hS.lam_E_fix e₃ he₃E he₃_lam
    have hconj_e₃ : r₃ * e₃ * r₃⁻¹ = u ^ 2 * e₃ := by
      have h2 : (t * u ^ 2) * (r₃ * e₃ * r₃⁻¹) = t * e₃ := by
        rw [← hr₃t]
        rw [show (r₃ * t * r₃⁻¹) * (r₃ * e₃ * r₃⁻¹) = r₃ * (t * e₃) * r₃⁻¹ by group,
          ← hr₃sq]
        group
      have h3 : u ^ 2 * (r₃ * e₃ * r₃⁻¹) = e₃ := by
        have h2' := h2
        rw [show (t * u ^ 2) * (r₃ * e₃ * r₃⁻¹) = t * (u ^ 2 * (r₃ * e₃ * r₃⁻¹))
            by group] at h2'
        exact mul_left_cancel h2'
      calc r₃ * e₃ * r₃⁻¹ = u ^ 2 * (u ^ 2 * (r₃ * e₃ * r₃⁻¹)) :=
            (fzbs_3g_u2_mul_u2 hS (r₃ * e₃ * r₃⁻¹)).symm
        _ = u ^ 2 * e₃ := by rw [h3]
    have he₃_notin_Z : e₃ ∉ Z := by
      intro hZ
      have hEq : u ^ 2 * e₃ = 1 * e₃ := by
        rw [one_mul, ← hconj_e₃]
        exact hS.R_Z r₃ hr₃R e₃ hZ
      exact hS.u_sq_ne (mul_right_cancel hEq)
    have he₃_sq : e₃ ^ 2 = u ^ 2 := by
      rcases fzbs_3g_zpowers_u_cases hS he₃u with h | h | h | h
      · exact absurd (by rw [h]; exact Subgroup.one_mem Z) he₃_notin_Z
      · rw [h]
      · exact absurd (by rw [h]; exact hS.E_sq u hS.u_mem) he₃_notin_Z
      · rw [h, pow_two (u ^ 3)]
        exact fzbs_3g_u3_mul hS
    have hs_inv_X : s * (t * e₃) * s⁻¹ = (t * e₃)⁻¹ := by
      have hte₃X : t * e₃ ∈ X := by rw [← hr₃sq]; exact hr₃sqX
      rcases hs with rfl | rfl
      · exact hS.tau_X (t * e₃) hte₃X
      · rw [show q * tau * (t * e₃) * (q * tau)⁻¹
            = q * (tau * (t * e₃) * tau⁻¹) * q⁻¹ by group, hS.tau_X (t * e₃) hte₃X]
        rw [show q * (t * e₃)⁻¹ * q⁻¹ = (t * e₃)⁻¹ by
          rw [hS.W_comm q hS.q_mem (t * e₃)⁻¹
            (Subgroup.inv_mem _ (hS.XW hte₃X))]; group]
    have hs_comm_sq : s * r₃ ^ 2 * s⁻¹ = r₃ ^ 2 := by
      rw [show s * r₃ ^ 2 * s⁻¹ = (s * r₃ * s⁻¹) ^ 2 by rw [conj_pow], hr₃s]
    have h_inv_eq : (t * e₃)⁻¹ = t * e₃ := by
      rw [← hs_inv_X, ← hr₃sq]
      exact hs_comm_sq
    have he₃_sq_one : e₃ ^ 2 = 1 := by
      have ht_inv : t⁻¹ = t :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hS.t_sq)
      have h := h_inv_eq
      rw [show (t * e₃)⁻¹ = t * e₃⁻¹ by
            rw [mul_inv_rev, ht_inv,
              ← hS.W_comm t (hS.XW hS.t_mem) e₃⁻¹
                (Subgroup.inv_mem _ (hS.XW (hS.EX he₃E)))]] at h
      have h2 : e₃⁻¹ = e₃ := mul_left_cancel h
      calc e₃ ^ 2 = e₃ * e₃ := by rw [pow_two]
        _ = e₃ * e₃⁻¹ := by rw [h2]
        _ = 1 := by rw [mul_inv_cancel]
    rw [he₃_sq] at he₃_sq_one
    exact hS.u_sq_ne he₃_sq_one

end CFSG.OddStandard.SmallF3.FritzII
