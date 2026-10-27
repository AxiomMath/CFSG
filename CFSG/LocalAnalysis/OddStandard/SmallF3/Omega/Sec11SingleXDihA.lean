module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXDih
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private lemma s11s_ca_conj_sq {t p : G} (ht : t * t = 1) :
    t * p ^ 2 * t = (t * p * t) ^ 2 := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h : t * p ^ 2 * t⁻¹ = (t * p * t⁻¹) ^ 2 :=
    (conj_pow (a := t) (b := p) (i := 2)).symm
  rwa [ht'] at h

private lemma s11s_ca_conj_inv_zpow {g z : G} (hg : g * g = 1) (hz : g * z * g = z⁻¹) (k : ℤ) :
    g * z ^ k * g = (z ^ k)⁻¹ := by
  have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hz' : g * z * g⁻¹ = z⁻¹ := by rw [hg']; exact hz
  have h : g * z ^ k * g⁻¹ = (z ^ k)⁻¹ := by
    rw [← conj_zpow, hz', inv_zpow]
  rwa [hg'] at h

private lemma s11s_ca_conj_inv_of_mem_zpowers {g y z : G} (hg : g * g = 1)
    (hz : g * z * g = z⁻¹) (hy : y ∈ zpowers z) : g * y * g = y⁻¹ := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← hk]
  exact s11s_ca_conj_inv_zpow hg hz k

private lemma s11s_ca_comm_zpow {g y : G} (h : g * y * g⁻¹ = y) (k : ℤ) :
    g * y ^ k = y ^ k * g := by
  have h1 : g * y ^ k * g⁻¹ = y ^ k := by rw [← conj_zpow, h]
  have h2 : g * y ^ k = y ^ k * g := by
    have := congrArg (· * g) h1
    simpa [mul_assoc] using this
  exact h2

private lemma s11s_ca_involutions_commute {s x : G} (hs : s * s = 1) (hx : x * x = 1)
    (h : (s * x) * (s * x) = 1) : x * s = s * x := by
  have hsx : (s * x)⁻¹ = s * x := inv_eq_of_mul_eq_one_right h
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hs, inv_eq_of_mul_eq_one_right hx] at hsx
  exact hsx

private lemma s11s_ca_conj_involution {g σ : G} (hσ : σ * σ = 1) :
    (g * σ * g⁻¹) * (g * σ * g⁻¹) = 1 := by
  rw [← pow_two, conj_pow, pow_two, hσ, mul_one, mul_inv_cancel]

private lemma s11s_ca_t_inv {t σ : G} (ht : t * t = 1) (hσ : σ * σ = 1) :
    t * (σ * t * σ⁻¹ * t) * t = (σ * t * σ⁻¹ * t)⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hσ' : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have h1 : t * (σ * t) * t = (σ * t)⁻¹ := by
    rw [mul_inv_rev, ht', hσ']
    calc t * (σ * t) * t = t * ((σ * t) * t) := by rw [mul_assoc]
      _ = t * (σ * (t * t)) := by rw [mul_assoc]
      _ = t * σ := by rw [ht, mul_one]
  rw [hσ', mul_assoc (σ * t) σ t, ← pow_two, s11s_ca_conj_sq ht, h1, inv_pow]

private lemma s11s_ca_sigma_inv {t σ : G} (ht : t * t = 1) (hσ : σ * σ = 1) :
    σ * (σ * t * σ⁻¹ * t) * σ = (σ * t * σ⁻¹ * t)⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hσ' : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have h1 : σ * (σ * t * σ⁻¹ * t) * σ = t * σ * t * σ := by
    calc σ * (σ * t * σ⁻¹ * t) * σ = (σ * σ) * t * σ⁻¹ * t * σ := by group
      _ = t * σ⁻¹ * t * σ := by rw [hσ, one_mul]
      _ = t * σ * t * σ := by rw [hσ']
  have h2 : (σ * t * σ⁻¹ * t)⁻¹ = t * σ * t * σ := by
    simp only [mul_inv_rev, inv_inv, ht', hσ']
    group
  rw [h1, h2]

private lemma s11s_ca_u_conj {s σ y : G} (hσy : σ * y * σ⁻¹ = y⁻¹)
    (hsy : s * y * s⁻¹ = y⁻¹) : (s * σ) * y * (s * σ)⁻¹ = y := by
  have h1 : (s * σ) * y * (s * σ)⁻¹ = s * (σ * y * σ⁻¹) * s⁻¹ := by group
  rw [h1, hσy, ← conj_inv, hsy, inv_inv]

private lemma s11s_ca_contra_odd {a c w : G} (haw : a * w = w * a)
    (hac : a * c * a⁻¹ = c⁻¹) (hw : w ∈ zpowers c) : w * w = 1 := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw
  have h1 : a * w * a⁻¹ = w := by rw [haw, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : a * w * a⁻¹ = w⁻¹ := by
    rw [← hm, ← conj_zpow, hac]
    simp only [inv_zpow]
  have : w = w⁻¹ := h1.symm.trans h2
  exact (inv_eq_iff_mul_eq_one).mp this.symm

theorem s11s_caseA_core {D : Subgroup G} {t s σ a w z : G}
    (ht : t * t = 1) (hs : s * s = 1) (hσ : σ * σ = 1)
    (hDσ : D = zpowers t ⊔ zpowers (σ * t * σ⁻¹)) (hDs : D = zpowers t ⊔ zpowers (s * t * s⁻¹))
    (hD2 : IsPGroup 2 ↥D) (hwD : w ∈ D) (hw4 : orderOf w = 4) (haw : a * w = w * a)
    (hcD : s * σ * (s * σ) ∈ D) (hac : a * (s * σ * (s * σ)) * a⁻¹ = (s * σ * (s * σ))⁻¹)
    (hzD : z ∈ D) (hz : ∀ d ∈ D, z * d = d * z)
    (hstar1 : σ * s * σ * s = s * (σ * s * σ) → σ * s * σ = s ∨ σ * s * σ = s * z)
    (hstar2 : ∀ d ∈ D, d⁻¹ * σ * d * s ≠ s * (d⁻¹ * σ * d)) : False := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hσ' : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  set y : G := σ * t * σ⁻¹ * t with hy
  set c : G := s * σ * (s * σ) with hc
  have htσ : (σ * t * σ⁻¹) * (σ * t * σ⁻¹) = 1 := by
    rw [← inv_eq_iff_mul_eq_one]
    simp only [conj_inv, inv_inv, ht']
  have ht_y : t * y * t = y⁻¹ := by
    rw [hy]
    exact s11s_ca_t_inv ht hσ
  have hσ_y : σ * y * σ⁻¹ = y⁻¹ := by
    rw [hσ', hy]
    exact s11s_ca_sigma_inv ht hσ
  have hyD : y ∈ D := by
    rw [hy]
    exact mul_mem (le_of_eq hDσ.symm (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
      (le_of_eq hDσ.symm (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  obtain ⟨n, hn⟩ := hD2 ⟨y, hyD⟩
  have hy2pow : y ^ 2 ^ n = 1 := by
    simpa [Subgroup.coe_pow] using congrArg (fun x : ↥D => (x : G)) hn
  have hw2 : w * w ≠ 1 := by
    intro h
    have h2 : orderOf w ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using h
    rw [hw4] at h2
    obtain ⟨q, hq⟩ := h2
    omega
  obtain ⟨kw, hkw | hkw⟩ := s11s_mem_pair ht htσ (le_of_eq hDσ hwD)
  · rw [← hy] at hkw
    have hy2 : y * y ≠ 1 := by
      intro h
      apply hw2
      have hy22z : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
      calc w * w = y ^ kw * y ^ kw := by rw [hkw]
        _ = y ^ (2 * kw) := by
              rw [← zpow_add]
              congr 1
              ring
        _ = (y ^ (2 : ℤ)) ^ kw := by rw [zpow_mul]
        _ = 1 := by rw [hy22z, one_zpow]
    have htσs : (s * t * s⁻¹) * (s * t * s⁻¹) = 1 := by
      rw [← inv_eq_iff_mul_eq_one]
      simp only [conj_inv, inv_inv, ht']
    have hy_mem_s : y ∈ zpowers (s * t * s⁻¹ * t) := by
      have heq : zpowers t ⊔ zpowers (σ * t * σ⁻¹) = zpowers t ⊔ zpowers (s * t * s⁻¹) :=
        hDσ.symm.trans hDs
      have h := s11s_mem_zpowers_pair ht htσ htσs heq (le_of_eq hDσ hwD) hw2
      rw [hy]
      exact h
    have hs_y0 : s * y * s = y⁻¹ :=
      s11s_ca_conj_inv_of_mem_zpowers hs (s11s_ca_sigma_inv ht hs) hy_mem_s
    have hs_y : s * y * s⁻¹ = y⁻¹ := by rw [hs']; exact hs_y0
    have hu_conj : (s * σ) * y * (s * σ)⁻¹ = y := s11s_ca_u_conj hσ_y hs_y
    have hz_mem : z ∈ zpowers y := by
      obtain ⟨kz, hkz | hkz⟩ := s11s_mem_pair ht htσ (le_of_eq hDσ hzD)
      · rw [← hy] at hkz
        exact Subgroup.mem_zpowers_iff.mpr ⟨kz, hkz.symm⟩
      · rw [← hy] at hkz
        exfalso
        have hcomm : z * y = y * z := hz y hyD
        rw [hkz] at hcomm
        have hzconj : z * y * z⁻¹ = y := by
          rw [hkz, hcomm, mul_assoc, mul_inv_cancel, mul_one]
        have hzinv : z * y * z⁻¹ = y⁻¹ := by
          rw [hkz, mul_inv_rev, ht']
          have h1 : (y ^ kz * t) * y * (t * (y ^ kz)⁻¹)
              = y ^ kz * (t * y * t) * (y ^ kz)⁻¹ := by group
          rw [h1, ht_y]
          group
        have hy_eq : y = y⁻¹ := hzconj.symm.trans hzinv
        exact hy2 ((inv_eq_iff_mul_eq_one).mp hy_eq.symm)
    have hc_mem : c ∈ zpowers y := by
      obtain ⟨kc, hkc | hkc⟩ := s11s_mem_pair ht htσ (le_of_eq hDσ hcD)
      · rw [← hy] at hkc
        exact Subgroup.mem_zpowers_iff.mpr ⟨kc, hkc.symm⟩
      · rw [← hy] at hkc
        have hcc : c * c = 1 := by
          rw [hkc]
          have h1 : (y ^ kc * t) * (y ^ kc * t) = y ^ kc * (t * y ^ kc * t) := by group
          rw [h1, s11s_ca_conj_inv_zpow ht ht_y kc, mul_inv_cancel]
        have hzσ : s * (s * σ) * s = (s * σ)⁻¹ := by
          rw [mul_inv_rev, hs', hσ']
          calc s * (s * σ) * s = (s * s) * σ * s := by group
            _ = σ * s := by rw [hs, one_mul]
        have hsc_inv : s * c * s⁻¹ = c⁻¹ := by
          rw [hs', hc]
          simpa only [zpow_two] using s11s_ca_conj_inv_zpow hs hzσ 2
        have hscs : s * c * s⁻¹ = c := by
          rw [hsc_inv, inv_eq_of_mul_eq_one_right hcc]
        have hsc : s * c = σ * s * σ := by
          rw [hc]
          calc s * ((s * σ) * (s * σ)) = (s * s) * σ * s * σ := by group
            _ = σ * s * σ := by rw [hs, one_mul]
        have hcomm_sc : c * s = s * c := by
          have h := congrArg (· * s) hscs
          rw [mul_assoc, inv_mul_cancel, mul_one] at h
          exact h.symm
        have hstar_lhs : (σ * s * σ) * s = s * (σ * s * σ) := by
          calc (σ * s * σ) * s = (s * c) * s := by rw [← hsc]
            _ = s * (c * s) := by group
            _ = s * (s * c) := by rw [hcomm_sc]
            _ = s * (σ * s * σ) := by rw [hsc]
        rcases hstar1 hstar_lhs with hcase | hcase
        · have hc1 : c = 1 := by
            have h : s * c = s * 1 := by rw [hsc, hcase, mul_one]
            exact mul_left_cancel h
          rw [hc1]
          exact Subgroup.one_mem _
        · have hcz : c = z := by
            have h : s * c = s * z := by rw [hsc, hcase]
            exact mul_left_cancel h
          rw [hcz]
          exact hz_mem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc_mem
    have hkeven : Even k := by
      by_contra hodd
      have hkodd : Odd k := Int.not_even_iff_odd.mp hodd
      have hymemc : y ∈ zpowers c := by
        rw [← hk]
        exact s11s_mem_zpowers_of_odd hy2pow hkodd
      have hwmemc : w ∈ zpowers c := by
        rw [hkw]
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hymemc
        exact Subgroup.mem_zpowers_iff.mpr ⟨m * kw, by rw [zpow_mul, hm]⟩
      exact hw2 (s11s_ca_contra_odd haw hac hwmemc)
    obtain ⟨j, hj⟩ := hkeven
    have hk2 : k = 2 * j := by omega
    obtain ⟨d, hdmem, hd⟩ := s11s_exists_conj_sq hσ ht (-j)
    have hdD : d ∈ D := le_of_eq hDσ.symm hdmem
    rw [← hy] at hd
    have hx : d⁻¹ * σ * d = σ * y ^ (-j) := by
      have h1 : σ * (σ * d⁻¹ * σ * d) = d⁻¹ * σ * d := by
        calc σ * (σ * d⁻¹ * σ * d) = (σ * σ) * d⁻¹ * σ * d := by group
          _ = d⁻¹ * σ * d := by rw [hσ, one_mul]
      have h2 := congrArg (fun x => σ * x) hd
      rw [h1] at h2
      exact h2
    have hsx : s * (d⁻¹ * σ * d) = (s * σ) * y ^ (-j) := by
      rw [hx]
      group
    have hue : (s * σ) * y ^ (-j) = y ^ (-j) * (s * σ) := s11s_ca_comm_zpow hu_conj (-j)
    have hu2 : ((s * σ) * y ^ (-j)) * ((s * σ) * y ^ (-j)) = 1 := by
      have h4 : ((s * σ) * y ^ (-j)) * ((s * σ) * y ^ (-j))
          = ((s * σ) * (s * σ)) * (y ^ (-j) * y ^ (-j)) := by
        calc ((s * σ) * y ^ (-j)) * ((s * σ) * y ^ (-j))
            = (s * σ) * (y ^ (-j) * (s * σ)) * y ^ (-j) := by group
          _ = (s * σ) * ((s * σ) * y ^ (-j)) * y ^ (-j) := by rw [← hue]
          _ = ((s * σ) * (s * σ)) * (y ^ (-j) * y ^ (-j)) := by group
      rw [h4]
      have hc2 : (s * σ) * (s * σ) = y ^ k := hc.symm.trans hk.symm
      rw [hc2, hk2]
      group
    have hx2 : (d⁻¹ * σ * d) * (d⁻¹ * σ * d) = 1 := by
      have hxd : d⁻¹ * σ * d = d⁻¹ * σ * (d⁻¹)⁻¹ := by rw [inv_inv]
      rw [hxd]
      exact s11s_ca_conj_involution hσ
    have hu2' : (s * (d⁻¹ * σ * d)) * (s * (d⁻¹ * σ * d)) = 1 := by
      rw [hsx]
      exact hu2
    exact hstar2 d hdD (s11s_ca_involutions_commute hs hx2 hu2')
  · rw [← hy] at hkw
    apply hw2
    rw [hkw]
    have h1 : (y ^ kw * t) * (y ^ kw * t) = y ^ kw * (t * y ^ kw * t) := by group
    rw [h1, s11s_ca_conj_inv_zpow ht ht_y kw, mul_inv_cancel]

end CFSG.OddStandard.SmallF3.Omega
