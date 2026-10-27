module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3D

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t q tau lam rho u : G} {Z E X W R T : Subgroup G}

private lemma fzbs_3f_A_mul {a b : G} :
    q⁻¹ * ((a * b) * q * (a * b)⁻¹)
      = (q⁻¹ * (a * q * a⁻¹)) * (a * (q⁻¹ * (b * q * b⁻¹)) * a⁻¹) := by
  group

private lemma fzbs_3f_A_inv {a : G} :
    q⁻¹ * (a⁻¹ * q * a) = a⁻¹ * (q⁻¹ * (a * q * a⁻¹))⁻¹ * a := by
  group

private lemma fzbs_3f_comm_mul (s a b : G) :
    ⁅s, a * b⁆ = ⁅s, a⁆ * (a * ⁅s, b⁆ * a⁻¹) := by
  rw [commutatorElement_def]; group

private lemma fzbs_3f_comm_inv (s a : G) :
    ⁅s, a⁻¹⁆ = a⁻¹ * ⁅s, a⁆⁻¹ * a := by
  rw [commutatorElement_def]; group

private lemma fzbs_3f_sq_mul (hS : FzbsStr t q tau lam rho u Z E X W R T) {a b : G}
    (ha : a ∈ W) (hb : b ∈ W) : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
  rw [pow_two, pow_two, pow_two]
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hS.W_comm b hb a ha]
    _ = a * a * (b * b) := by group

private lemma fzbs_3f_conj_mem_E (hS : FzbsStr t q tau lam rho u Z E X W R T)
    {g₁ g₂ x : G} (hg₁ : g₁ ∈ R) (hg₂ : g₂ ∈ zpowers rho) (hx : x ∈ X) :
    x * (g₁ * (g₂ * (g₁⁻¹ * x⁻¹ * g₁) * g₂⁻¹) * g₁⁻¹) ∈ E := by
  have hxinvW : x⁻¹ ∈ W := W.inv_mem (hS.XW hx)
  obtain ⟨z₁, hz₁Z, h1⟩ : ∃ z ∈ Z, g₁⁻¹ * x⁻¹ * g₁ = x⁻¹ * z := by
    have hz : g₁⁻¹ * x⁻¹ * g₁ * x ∈ Z := by
      have h := fzbs_comm_X hS (R.inv_mem hg₁) (X.inv_mem hx)
      simpa using h
    refine ⟨g₁⁻¹ * x⁻¹ * g₁ * x, hz, ?_⟩
    calc g₁⁻¹ * x⁻¹ * g₁
        = (g₁⁻¹ * x⁻¹ * g₁ * x) * x⁻¹ := by group
      _ = x⁻¹ * (g₁⁻¹ * x⁻¹ * g₁ * x) := by
            rw [hS.W_comm (g₁⁻¹ * x⁻¹ * g₁ * x) (hS.XW (hS.EX (hS.ZE hz)))
              x⁻¹ hxinvW]
  obtain ⟨e₂, he₂E, h2⟩ : ∃ e ∈ E, g₂ * (x⁻¹ * z₁) * g₂⁻¹ = x⁻¹ * e := by
    have he : g₂ * x⁻¹ * g₂⁻¹ * x ∈ E := by
      have h := fzbs_rho_X_E hS hg₂ (X.inv_mem hx)
      simpa using h
    have hz' : g₂ * z₁ * g₂⁻¹ ∈ Z := fzbs_zpow_conj hS.rho_cube hS.rho_Z hg₂ hz₁Z
    have h2a : g₂ * x⁻¹ * g₂⁻¹ = x⁻¹ * (g₂ * x⁻¹ * g₂⁻¹ * x) := by
      calc g₂ * x⁻¹ * g₂⁻¹ = (g₂ * x⁻¹ * g₂⁻¹ * x) * x⁻¹ := by group
        _ = x⁻¹ * (g₂ * x⁻¹ * g₂⁻¹ * x) := by
              rw [hS.W_comm (g₂ * x⁻¹ * g₂⁻¹ * x) (hS.XW (hS.EX he)) x⁻¹ hxinvW]
    refine ⟨(g₂ * x⁻¹ * g₂⁻¹ * x) * (g₂ * z₁ * g₂⁻¹), E.mul_mem he (hS.ZE hz'), ?_⟩
    calc g₂ * (x⁻¹ * z₁) * g₂⁻¹
        = (g₂ * x⁻¹ * g₂⁻¹) * (g₂ * z₁ * g₂⁻¹) := by group
      _ = (x⁻¹ * (g₂ * x⁻¹ * g₂⁻¹ * x)) * (g₂ * z₁ * g₂⁻¹) := by
            conv_lhs => rw [h2a]
      _ = x⁻¹ * ((g₂ * x⁻¹ * g₂⁻¹ * x) * (g₂ * z₁ * g₂⁻¹)) := by group
  obtain ⟨e₃, he₃E, h3⟩ : ∃ e ∈ E, g₁ * (x⁻¹ * e₂) * g₁⁻¹ = x⁻¹ * e := by
    have hc : g₁ * x⁻¹ * g₁⁻¹ * x ∈ Z := by
      have h := fzbs_comm_X hS hg₁ (X.inv_mem hx)
      simpa using h
    have he : g₁ * e₂ * g₁⁻¹ ∈ E := fzbs_R_E hS hg₁ he₂E
    have h3a : g₁ * x⁻¹ * g₁⁻¹ = x⁻¹ * (g₁ * x⁻¹ * g₁⁻¹ * x) := by
      calc g₁ * x⁻¹ * g₁⁻¹ = (g₁ * x⁻¹ * g₁⁻¹ * x) * x⁻¹ := by group
        _ = x⁻¹ * (g₁ * x⁻¹ * g₁⁻¹ * x) := by
              rw [hS.W_comm (g₁ * x⁻¹ * g₁⁻¹ * x) (hS.XW (hS.EX (hS.ZE hc)))
                x⁻¹ hxinvW]
    refine ⟨(g₁ * x⁻¹ * g₁⁻¹ * x) * (g₁ * e₂ * g₁⁻¹), E.mul_mem (hS.ZE hc) he, ?_⟩
    calc g₁ * (x⁻¹ * e₂) * g₁⁻¹
        = (g₁ * x⁻¹ * g₁⁻¹) * (g₁ * e₂ * g₁⁻¹) := by group
      _ = (x⁻¹ * (g₁ * x⁻¹ * g₁⁻¹ * x)) * (g₁ * e₂ * g₁⁻¹) := by
            conv_lhs => rw [h3a]
      _ = x⁻¹ * ((g₁ * x⁻¹ * g₁⁻¹ * x) * (g₁ * e₂ * g₁⁻¹)) := by group
  rw [h1, h2, h3]
  rw [show x * (x⁻¹ * e₃) = e₃ from by group]
  exact he₃E

theorem fzbs_P_aq (hS : FzbsStr t q tau lam rho u Z E X W R T) {p : G}
    (hp : p ∈ ⁅R, zpowers rho⁆) : q⁻¹ * (p * q * p⁻¹) ∈ E := by
  classical
  let M : Subgroup G :=
    { carrier := {g : G | g ∈ R ∧ q⁻¹ * (g * q * g⁻¹) ∈ E}
      one_mem' := by
        refine ⟨R.one_mem, ?_⟩
        simp
      mul_mem' := by
        rintro a b ⟨haR, haE⟩ ⟨hbR, hbE⟩
        refine ⟨R.mul_mem haR hbR, ?_⟩
        rw [fzbs_3f_A_mul]
        exact E.mul_mem haE (fzbs_R_E hS haR hbE)
      inv_mem' := by
        rintro a ⟨haR, haE⟩
        refine ⟨R.inv_mem haR, ?_⟩
        simp only [inv_inv]
        rw [fzbs_3f_A_inv]
        simpa using fzbs_R_E hS (R.inv_mem haR) (E.inv_mem haE) }
  have hPM : ⁅R, zpowers rho⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨fzbs_P_le_R hS (Subgroup.commutator_mem_commutator hg₁ hg₂), ?_⟩
    have hcq : Commute rho q := by
      rw [commute_iff_eq]
      calc rho * q = (rho * q * rho⁻¹) * rho := by group
        _ = q * rho := by rw [hS.rho_q]
    have hcg₂q : Commute g₂ q := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
      exact hcq.zpow_left k
    have hA2 : q⁻¹ * (g₂ * q * g₂⁻¹) = 1 := by rw [hcg₂q.eq]; group
    have hA2inv : q⁻¹ * (g₂⁻¹ * q * (g₂⁻¹)⁻¹) = 1 := by
      rw [hcg₂q.inv_left.eq]; group
    have hAh : q⁻¹ * ((g₂ * g₁⁻¹ * g₂⁻¹) * q * (g₂ * g₁⁻¹ * g₂⁻¹)⁻¹)
        = g₂ * (q⁻¹ * (g₁⁻¹ * q * g₁)) * g₂⁻¹ := by
      have e : g₂ * g₁⁻¹ * g₂⁻¹ = g₂ * (g₁⁻¹ * g₂⁻¹) := by group
      rw [e, fzbs_3f_A_mul, fzbs_3f_A_mul, hA2, hA2inv]
      group
    have hAaq : q⁻¹ * (⁅g₁, g₂⁆ * q * ⁅g₁, g₂⁆⁻¹)
        = (q⁻¹ * (g₁ * q * g₁⁻¹))
          * (g₁ * (g₂ * (g₁⁻¹ * (q⁻¹ * (g₁ * q * g₁⁻¹))⁻¹ * g₁) * g₂⁻¹)
              * g₁⁻¹) := by
      have e : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e, fzbs_3f_A_mul, hAh, fzbs_3f_A_inv]
    rw [hAaq]
    exact fzbs_3f_conj_mem_E hS hg₁ hg₂ (fzbs_aq hS hg₁).1
  exact (hPM hp).2

theorem fzbs_P_tau (hS : FzbsStr t q tau lam rho u Z E X W R T) {p : G}
    (hp : p ∈ ⁅R, zpowers rho⁆) : ⁅tau, p⁆ ∈ E := by
  classical
  let M : Subgroup G :=
    { carrier := {g : G | g ∈ R ∧ ⁅tau, g⁆ ∈ E}
      one_mem' := by
        refine ⟨R.one_mem, ?_⟩
        simp [commutatorElement_def]
      mul_mem' := by
        rintro a b ⟨haR, haE⟩ ⟨hbR, hbE⟩
        refine ⟨R.mul_mem haR hbR, ?_⟩
        rw [fzbs_3f_comm_mul]
        exact E.mul_mem haE (fzbs_R_E hS haR hbE)
      inv_mem' := by
        rintro a ⟨haR, haE⟩
        refine ⟨R.inv_mem haR, ?_⟩
        rw [fzbs_3f_comm_inv]
        simpa using fzbs_R_E hS (R.inv_mem haR) (E.inv_mem haE) }
  have hPM : ⁅R, zpowers rho⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨fzbs_P_le_R hS (Subgroup.commutator_mem_commutator hg₁ hg₂), ?_⟩
    have hct : Commute tau rho := hS.tau_rho
    have hcg₂t : Commute g₂ tau := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
      exact hct.symm.zpow_left k
    have hC2 : ⁅tau, g₂⁆ = 1 := by
      rw [commutatorElement_def, ← hcg₂t.eq]; group
    have hC2inv : ⁅tau, g₂⁻¹⁆ = 1 := by
      rw [commutatorElement_def,
        show tau * g₂⁻¹ = g₂⁻¹ * tau from hcg₂t.symm.inv_right.eq]
      group
    have hCh : ⁅tau, g₂ * g₁⁻¹ * g₂⁻¹⁆ = g₂ * ⁅tau, g₁⁻¹⁆ * g₂⁻¹ := by
      have e : g₂ * g₁⁻¹ * g₂⁻¹ = g₂ * (g₁⁻¹ * g₂⁻¹) := by group
      rw [e, fzbs_3f_comm_mul, fzbs_3f_comm_mul, hC2, hC2inv]
      group
    have hC : ⁅tau, ⁅g₁, g₂⁆⁆
        = ⁅tau, g₁⁆ * (g₁ * (g₂ * (g₁⁻¹ * ⁅tau, g₁⁆⁻¹ * g₁) * g₂⁻¹) * g₁⁻¹) := by
      have e : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e, fzbs_3f_comm_mul, hCh, fzbs_3f_comm_inv]
    rw [hC]
    exact fzbs_3f_conj_mem_E hS hg₁ hg₂ (fzbs_tau_comm_X hS hg₁)
  exact (hPM hp).2

theorem fzbs_P_ker (hS : FzbsStr t q tau lam rho u Z E X W R T) {p : G}
    (hp : p ∈ ⁅R, zpowers rho⁆) (hpt : p * t * p⁻¹ = t) : p ∈ X := by
  have hpR : p ∈ R := fzbs_P_le_R hS hp
  have hchi : t * (p * t * p⁻¹) = 1 := by rw [hpt, ← pow_two, hS.t_sq]
  have hqinv : q⁻¹ * q⁻¹ = t := by
    rw [← mul_inv_rev, ← pow_two, hS.q_sq]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hS.t_sq)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hS.t_sq)
  rcases (fzbs_chi_eq_one hS hpR).mp hchi with hpW | hpτW
  · rcases hS.W_split p hpW with hpX | hqpX
    · exact hpX
    · exfalso
      have hyW : q * p ∈ W := hS.XW hqpX
      have hq2 : (q⁻¹) ^ 2 = t := by rw [pow_two]; exact hqinv
      have hp2 : p ^ 2 = t * (q * p) ^ 2 := by
        have e : p = q⁻¹ * (q * p) := by group
        conv_lhs => rw [e]
        rw [fzbs_3f_sq_mul hS (W.inv_mem hS.q_mem) hyW, hq2]
      have htau_p_eq : ⁅tau, p⁆ = (p ^ 2)⁻¹ := by
        rw [commutatorElement_def, fzbs_tau_W hS hpW, pow_two]
        group
      have hp2inv : (p ^ 2)⁻¹ = t * ((q * p) ^ 2)⁻¹ := by
        rw [hp2, mul_inv_rev, htinv]
        exact hS.W_comm ((q * p) ^ 2)⁻¹ (W.inv_mem (pow_mem hyW 2)) t
          (hS.XW hS.t_mem)
      have ht : t = ⁅tau, p⁆ * (q * p) ^ 2 := by
        rw [htau_p_eq, hp2inv]; group
      have hy2Z : (q * p) ^ 2 ∈ Z := (hS.X_iff (q * p) hyW).mp hqpX
      refine hS.t_notin_E ?_
      rw [ht]
      exact E.mul_mem (fzbs_P_tau hS hp) (hS.ZE hy2Z)
  · exfalso
    have hp_eq : p = (p * tau⁻¹) * tau := by group
    have h1 : ((p * tau⁻¹) * tau) * q * ((p * tau⁻¹) * tau)⁻¹
        = (p * tau⁻¹) * q⁻¹ * (p * tau⁻¹)⁻¹ := by
      rw [show ((p * tau⁻¹) * tau) * q * ((p * tau⁻¹) * tau)⁻¹
            = (p * tau⁻¹) * (tau * q * tau⁻¹) * (p * tau⁻¹)⁻¹ from by group,
          fzbs_tau_inv_q hS]
    have hap : q⁻¹ * (p * q * p⁻¹) = t := by
      calc q⁻¹ * (p * q * p⁻¹)
          = q⁻¹ * (((p * tau⁻¹) * tau) * q * ((p * tau⁻¹) * tau)⁻¹) := by
            conv_lhs => rw [hp_eq]
        _ = q⁻¹ * ((p * tau⁻¹) * q⁻¹ * (p * tau⁻¹)⁻¹) := by rw [h1]
        _ = q⁻¹ * q⁻¹ := by
              rw [hS.W_comm (p * tau⁻¹) hpτW q⁻¹ (W.inv_mem hS.q_mem)]
              group
        _ = t := hqinv
    refine hS.t_notin_E ?_
    rw [← hap]
    exact fzbs_P_aq hS hp

theorem fzbs_P_chi_surj (hS : FzbsStr t q tau lam rho u Z E X W R T) {z : G} (hz : z ∈ Z) :
    ∃ p ∈ ⁅R, zpowers rho⁆, p * t * p⁻¹ = t * z := by
  obtain ⟨r, hr, hrt⟩ := hS.R_t_surj z hz
  obtain ⟨c, hcR, hc_fix, hcP⟩ :=
    fzl_coprime_decomp hS.pgroup_R hS.rho_cube hS.rho_R hr
  have hchi : t * (c * t * c⁻¹) = 1 := by
    by_contra hne
    have hfix : rho * (t * (c * t * c⁻¹)) * rho⁻¹ = t * (c * t * c⁻¹) := by
      have h := fzbs_chi_conj (g := rho) (r := c) hS.rho_t
      rw [hc_fix] at h
      exact h.symm
    exact hS.rho_Z_fpf (t * (c * t * c⁻¹)) (hS.R_t c hcR) hne hfix
  have hct : c * t * c⁻¹ = t := by
    have h := congrArg (fun x => t * x) hchi
    rw [mul_one] at h
    rw [← mul_assoc, ← pow_two, hS.t_sq, one_mul] at h
    exact h
  have hct' : c⁻¹ * t * c = t := by
    have h := congrArg (fun x => c⁻¹ * x * c) hct
    simpa [mul_assoc] using h.symm
  have hcz : c⁻¹ * z * c = z := by
    have h := hS.R_Z c⁻¹ (R.inv_mem hcR) z hz
    simpa using h
  refine ⟨c⁻¹ * r, hcP, ?_⟩
  calc (c⁻¹ * r) * t * (c⁻¹ * r)⁻¹
      = c⁻¹ * (r * t * r⁻¹) * c := by group
    _ = c⁻¹ * (t * z) * c := by rw [hrt]
    _ = (c⁻¹ * t * c) * (c⁻¹ * z * c) := by group
    _ = t * z := by rw [hct', hcz]

end CFSG.OddStandard.SmallF3.FritzII
