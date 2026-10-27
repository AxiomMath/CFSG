module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step5
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4f

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace Q3Data

variable (d : Q3Data H)
include d

theorem b_conj_xgx (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    (h.x * d.g * h.x)⁻¹ * d.b * (h.x * d.g * h.x) = d.tau * d.z * d.b := by
  have key : ∀ s u v : X, s⁻¹ * (u * v) * s = (s⁻¹ * u * s) * (s⁻¹ * v * s) := fun s u v => by
    group
  have hgb : d.g⁻¹ * d.b * d.g = d.b := by
    have := mem_centralizer_singleton_iff.mp (d.K_le_centralizer_b d.g_K)
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  have e2 : d.g⁻¹ * (h.a * d.b) * d.g = h.a * d.tau * d.b := by
    rw [key, d.a_g, hgb]
  have e3 : h.x⁻¹ * (h.a * d.tau * d.b) * h.x = h.a * (d.tau * d.z) * (h.a * d.b) := by
    rw [key, key, H.a_x, d.tz_eq_conj hq hF, d.xbx]
  have hta := d.tau_comm_a
  have hza := d.z_comm_a
  have h1 : h.a * (d.tau * d.z) = d.tau * d.z * h.a := by
    rw [← mul_assoc, ← hta, mul_assoc, ← hza, ← mul_assoc]
  rw [show (h.x * d.g * h.x)⁻¹ * d.b * (h.x * d.g * h.x) =
      h.x⁻¹ * (d.g⁻¹ * (h.x⁻¹ * d.b * h.x) * d.g) * h.x by group, d.xbx, e2, e3, h1]
  calc d.tau * d.z * h.a * (h.a * d.b) = d.tau * d.z * (h.a * h.a) * d.b := by group
    _ = d.tau * d.z * d.b := by rw [Six.a_mul_a_self h, mul_one]

theorem E0_conj (hq : h.IsQ3) (hF : Cat8.Q3Facts) {e : X} (he : e ∈ d.E0) :
    e = 1 ∨ ∃ g : X, g⁻¹ * (d.tau * d.z) * g = e := by
  obtain ⟨c, hc⟩ := d.exists_z_conj_tz hq hF
  have hzt : d.z * d.tau = d.tau * d.z := (d.tau_comm_z hF.simple hF.inner).symm
  rcases d.E0_cases hq hF.simple hF.inner hF.out he with h1 | ⟨n, -, hn⟩ | ⟨n, -, hn⟩
  · exact Or.inl h1
  · right
    refine ⟨c⁻¹ * n, ?_⟩
    rw [← hn, ← hc]
    group
  · right
    exact ⟨n, by rw [← hzt]; exact hn⟩

theorem conj_b_NME0 {n : X} (hn : n ∈ d.NME0) : n⁻¹ * d.b * n = d.b := by
  have := mem_centralizer_singleton_iff.mp (d.NME0_le_centralizer_b hn)
  rw [mul_assoc, ← this, inv_mul_cancel_left]

theorem Eb_conj (hq : h.IsQ3) (hF : Cat8.Q3Facts) {e : X} (he : e ∈ d.E0) :
    (∃ g : X, g⁻¹ * d.b * g = e * d.b) ∨ ∃ g : X, g⁻¹ * (d.b * d.z) * g = e * d.b := by
  have htz : d.tau * d.z = d.z * d.tau := d.tau_comm_z hF.simple hF.inner
  rcases d.E0_cases hq hF.simple hF.inner hF.out he with rfl | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · left
    exact ⟨1, by group⟩
  · right
    refine ⟨n, ?_⟩
    calc n⁻¹ * (d.b * d.z) * n = (n⁻¹ * d.z * n) * (n⁻¹ * d.b * n) := by
          rw [d.b_comm_z]
          group
      _ = n⁻¹ * d.z * n * d.b := by rw [d.conj_b_NME0 hn]
  · left
    refine ⟨h.x * d.g * h.x * n, ?_⟩
    calc (h.x * d.g * h.x * n)⁻¹ * d.b * (h.x * d.g * h.x * n) =
          n⁻¹ * ((h.x * d.g * h.x)⁻¹ * d.b * (h.x * d.g * h.x)) * n := by group
      _ = n⁻¹ * (d.tau * d.z * d.b) * n := by rw [d.b_conj_xgx hq hF]
      _ = n⁻¹ * (d.z * d.tau) * n * (n⁻¹ * d.b * n) := by
          rw [htz]
          group
      _ = n⁻¹ * (d.z * d.tau) * n * d.b := by rw [d.conj_b_NME0 hn]

theorem a_not_conj_E (hq : h.IsQ3) (hF : Cat8.Q3Facts) (g : X) {y : X} (hy : y ∈ d.E) :
    g⁻¹ * h.a * g ≠ y := by
  have hnf := d.not_fused hq hF
  have ha1 : h.a ≠ 1 := fun h1 => H.a_not_mem_K hF.simple hF.inner (h1 ▸ one_mem _)
  obtain ⟨e, he, rfl | rfl⟩ := d.mem_E_cases hy
  · rcases d.E0_conj hq hF he with rfl | ⟨c, rfl⟩
    · intro h1
      apply ha1
      calc h.a = g * (g⁻¹ * h.a * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro h1
      apply (hnf (g * c⁻¹)).2.2.1
      rw [show (g * c⁻¹)⁻¹ * h.a * (g * c⁻¹) = c * (g⁻¹ * h.a * g) * c⁻¹ by group, h1]
      group
  · rcases d.Eb_conj hq hF he with ⟨c, hc⟩ | ⟨c, hc⟩
    · intro h1
      apply (hnf (g * c⁻¹)).1
      rw [show (g * c⁻¹)⁻¹ * h.a * (g * c⁻¹) = c * (g⁻¹ * h.a * g) * c⁻¹ by group, h1, ← hc]
      group
    · intro h1
      apply (hnf (g * c⁻¹)).2.1
      rw [show (g * c⁻¹)⁻¹ * h.a * (g * c⁻¹) = c * (g⁻¹ * h.a * g) * c⁻¹ by group, h1, ← hc]
      group

theorem E0_strongly_closed (hq : h.IsQ3) (hF : Cat8.Q3Facts) {e : X} (he : e ∈ d.E0) (g : X)
    (hg : g⁻¹ * e * g ∈ d.E) : g⁻¹ * e * g ∈ d.E0 := by
  have hnf := d.not_fused hq hF
  obtain ⟨e', he', h1 | h1⟩ := d.mem_E_cases hg
  · rw [h1]
    exact he'
  · exfalso
    rcases d.E0_conj hq hF he with rfl | ⟨c, rfl⟩
    · have hb : d.b = e'⁻¹ := by
        have h2 : (1 : X) = e' * d.b := by
          rw [← h1]
          group
        calc d.b = e'⁻¹ * (e' * d.b) := by group
          _ = e'⁻¹ := by rw [← h2, mul_one]
      have hbM : d.b ∈ h.M3 := by
        rw [hb]
        exact inv_mem (d.E0_le_M3 he')
      exact d.b_not_mem_M3 hF.simple hF.inner hbM
    · rcases d.Eb_conj hq hF he' with ⟨k, hk⟩ | ⟨k, hk⟩
      · apply (hnf (k * (c * g)⁻¹)).2.2.2.2.1
        rw [show (k * (c * g)⁻¹)⁻¹ * d.b * (k * (c * g)⁻¹) =
          (c * g) * (k⁻¹ * d.b * k) * (c * g)⁻¹ by group, hk, ← h1]
        group
      · apply (hnf (k * (c * g)⁻¹)).2.2.2.2.2
        rw [show (k * (c * g)⁻¹)⁻¹ * (d.b * d.z) * (k * (c * g)⁻¹) =
          (c * g) * (k⁻¹ * (d.b * d.z) * k) * (c * g)⁻¹ by group, hk, ← h1]
        group

theorem R_cases {y : X} (hy : y ∈ d.R) : ∃ r ∈ d.RM, y = r ∨ y = r * d.b := by
  have hy' : y ∈ d.RM ⊔ zpowers d.b := by
    rw [← d.B_eq]
    exact hy
  have hbN : d.b ∈ normalizer (d.RM : Set X) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      d.b_comm_of_mem_M3 (d.RM_le hr))
  exact Eight.mem_sup_zpowers_cases hbN d.b_mul_self hy'

theorem mem_RM_of_mem_R (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y : X}
    (hy : y ∈ d.R) (hyM : y ∈ h.M3) : y ∈ d.RM := by
  obtain ⟨r, hr, rfl | rfl⟩ := d.R_cases hy
  · exact hr
  · exfalso
    apply d.b_not_mem_M3 hCF1 hCF2
    have := mul_mem (inv_mem (d.RM_le hr)) hyM
    rwa [inv_mul_cancel_left] at this

theorem RM_le_R : d.RM ≤ d.R := le_sup_left

theorem rh_mem_cR {r : X} (hr : r ∈ d.RM) : d.rh r hr ∈ d.c.R := by
  rw [d.c_R]
  exact mem_map_of_mem H.rho (show (⟨r, d.RM_le hr⟩ : ↥h.M3) ∈ d.RM.subgroupOf h.M3 from hr)

theorem mem_E0_of_comm (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {r : X}
    (hr : r ∈ d.RM) (hc : ∀ e ∈ d.E0, r * e = e * r) : r ∈ d.E0 := by
  refine (d.mem_E0_iff hr).mpr ?_
  rw [← d.centralizer_E0hat, mem_centralizer_iff]
  intro w hw
  obtain ⟨e, he, rfl⟩ := d.exists_rh_E0 hw
  exact ((d.comm_iff hCF1 hCF2 hr (d.E0_le_RM he)).mp (hc e he)).symm

theorem eq_E_of_normal (hq : h.IsQ3) (hF : Cat8.Q3Facts) {A : Subgroup X} (hAR : A ≤ d.R)
    (hA2 : ∀ y ∈ A, y * y = 1) (hA32 : Nat.card A = 32)
    (hAn : ∀ r ∈ d.R, ∀ y ∈ A, r * y * r⁻¹ ∈ A)
    (ha : ∀ y ∈ A, ∀ g : X, g⁻¹ * h.a * g ≠ y) : A = d.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  set A0 : Subgroup X := A ⊓ h.M3 with hA0
  have hA0RM : A0 ≤ d.RM := fun y hy =>
    d.mem_RM_of_mem_R hCF1 hCF2 (hAR (Subgroup.mem_inf.mp hy).1) (Subgroup.mem_inf.mp hy).2
  have hA0M : A0 ≤ h.M3 := inf_le_right
  have hidx : Nat.card A ≤ 2 * Nat.card A0 := by
    refine Eight.card_le_two_mul_card_inf fun y hy y' hy' hyM hy'M => ?_
    obtain ⟨r, hr, hyr⟩ := d.R_cases (hAR hy)
    obtain ⟨r', hr', hyr'⟩ := d.R_cases (hAR hy')
    rcases hyr with rfl | rfl
    · exact absurd (d.RM_le hr) hyM
    rcases hyr' with rfl | rfl
    · exact absurd (d.RM_le hr') hy'M
    have hrb := d.b_comm_of_mem_M3 (mul_mem (inv_mem (d.RM_le hr)) (d.RM_le hr'))
    rw [show (r * d.b)⁻¹ * (r' * d.b) = d.b⁻¹ * ((r⁻¹ * r') * d.b) by group, hrb,
      inv_mul_cancel_left]
    exact mul_mem (inv_mem (d.RM_le hr)) (d.RM_le hr')
  set Ahat := (A0.subgroupOf h.M3).map H.rho with hAhat
  have hA0p : IsPGroup 2 (A0.subgroupOf h.M3) := (d.isPGroup_RM.to_le hA0RM).comap_subtype
  have hcardAhat : Nat.card Ahat = Nat.card A0 := by
    rw [hAhat, Eight.card_map_of_isPGroup hker hA0p, ← card_map_of_injective h.M3.subtype_injective,
      map_subgroupOf_eq_of_le hA0M]
  have hAhatR : Ahat ≤ d.c.R := by
    rintro _ ⟨m, hm, rfl⟩
    exact d.rh_mem_cR (hA0RM hm)
  have hAhat2 : Cat8.IsElemAb2 Ahat := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul, ← map_one H.rho]
    congr 1
    exact Subtype.ext (hA2 _ (Subgroup.mem_inf.mp hm).1)
  have hA0le : Nat.card A0 ∣ 32 := hA32 ▸ card_dvd_of_le inf_le_left
  obtain ⟨k, hk5, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card A0 ∣ 2 ^ 5 from hA0le)
  have hA0_16 : Nat.card A0 = 16 := by
    have hk4 : 4 ≤ k := by
      by_contra hlt
      push Not at hlt
      interval_cases k <;> (rw [hA32, hk] at hidx; norm_num at hidx)
    interval_cases k
    · rw [hk]
      norm_num
    · exfalso
      apply d.c_props.no_E32 Ahat hAhatR hAhat2
      rw [hcardAhat, hk]
      norm_num
  have hAhatn : (Ahat.subgroupOf d.c.R).Normal := by
    constructor
    intro n hn g
    have hg : (g : MulAut (h.K ⧸ pPrimeCore 2 h.K)) ∈ (d.RM.subgroupOf h.M3).map H.rho :=
      d.c_R.le g.2
    obtain ⟨r, hr, hrg⟩ := mem_map.mp hg
    have hn' : (n : MulAut (h.K ⧸ pPrimeCore 2 h.K)) ∈ Ahat := hn
    obtain ⟨m, hm, hmn⟩ := mem_map.mp hn'
    show (g : MulAut (h.K ⧸ pPrimeCore 2 h.K)) * (n : MulAut (h.K ⧸ pPrimeCore 2 h.K)) *
      (g : MulAut (h.K ⧸ pPrimeCore 2 h.K))⁻¹ ∈ Ahat
    rw [← hrg, ← hmn, ← map_inv, ← map_mul, ← map_mul]
    refine mem_map_of_mem H.rho (Subgroup.mem_inf.mpr ⟨?_, (r * m * r⁻¹).2⟩)
    exact hAn _ (d.RM_le_R hr) _ (Subgroup.mem_inf.mp hm).1
  rcases d.E0hat_normal hAhatR hAhat2 (by rw [hcardAhat, hA0_16]) hAhatn with hE | ⟨w, hw, y, hy⟩
  ·
    have hA0E0 : A0 ≤ d.E0 := fun u hu => by
      refine (d.mem_E0_iff (hA0RM hu)).mpr ?_
      rw [← hE]
      exact mem_map_of_mem H.rho (show (⟨u, hA0M hu⟩ : ↥h.M3) ∈ A0.subgroupOf h.M3 from hu)
    have hA0eq : A0 = d.E0 :=
      eq_of_le_of_card_ge hA0E0 (by rw [d.card_E0 hCF1 hCF2, hA0_16])
    have hE0A : d.E0 ≤ A := by
      rw [← hA0eq]
      exact inf_le_left
    have hAE : A ≤ d.E := by
      intro y hy
      obtain ⟨r, hr, hyr | hyr⟩ := d.R_cases (hAR hy)
      · rw [hyr] at hy ⊢
        have hrA0 : r ∈ A0 := Subgroup.mem_inf.mpr ⟨hy, d.RM_le hr⟩
        rw [hA0eq] at hrA0
        exact d.E0_le_E hrA0
      · rw [hyr] at hy ⊢
        have hrE0 : r ∈ d.E0 := by
          refine d.mem_E0_of_comm hCF1 hCF2 hr fun e he => ?_
          have h1 := Eight.comm_of_mul_self hA2 hy (hE0A he)
          have hb := d.b_comm_E0 he
          have h2 : r * e * d.b = e * r * d.b := by
            calc r * e * d.b = r * (e * d.b) := by group
              _ = r * (d.b * e) := by rw [hb]
              _ = r * d.b * e := by group
              _ = e * (r * d.b) := h1
              _ = e * r * d.b := by group
          exact mul_right_cancel h2
        exact mul_mem (d.E0_le_E hrE0) d.b_mem_E
    exact eq_of_le_of_card_ge hAE (by rw [hA32, d.card_E hCF1 hCF2])
  ·
    exfalso
    obtain ⟨m, hm, rfl⟩ := mem_map.mp hw
    obtain ⟨y', rfl⟩ := H.rho_surjective hq hCF1 hCF2 hF.out y
    have hm2 : (m : X) * m = 1 := hA2 _ (Subgroup.mem_inf.mp hm).1
    have hu : IsPGroup 2 (zpowers h.aM) := isPGroup_zpowers_of_mul_self h.aM_mul_self
    have hv : IsPGroup 2 (zpowers m) :=
      isPGroup_zpowers_of_mul_self (Subtype.ext hm2 : m * m = 1)
    obtain ⟨c, -, hc⟩ := Eight.exists_conj_eq_of_map hker hu hv y'
      (by rw [← hy, d.c_a, H.rho_aM])
    apply ha _ (Subgroup.mem_inf.mp hm).1 c
    exact (congrArg Subtype.val hc).symm

theorem orderOf_ctz (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) : orderOf (d.c.tau * d.c.z) = 2 := by
  have htz : d.tau * d.z ∈ d.RM := mul_mem d.tau_mem_RM d.z_mem_RM
  have hrtz : d.rh (d.tau * d.z) htz = d.c.tau * d.c.z := by
    rw [d.rh_mul d.tau_mem_RM d.z_mem_RM, d.rh_tau, d.rh_z]
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, ← hrtz, ← d.rh_mul, ← d.rh_one]
    simp only [rh]
    congr 1
    exact Subtype.ext (d.tz_mul_self hCF1 hCF2)
  · rw [← hrtz, ← d.rh_one]
    intro h1
    have h2 := d.rho_inj hCF1 hCF2 htz (one_mem _) h1
    apply d.tau_ne_z hq hCF1 hCF2 hL0
    calc d.tau = d.tau * d.z * d.z := by rw [mul_assoc, d.z_sq, mul_one]
      _ = d.z := by rw [h2, one_mul]

theorem mem_center_R (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) {y : X} (hy : y ∈ d.R) (hc : ∀ r ∈ d.R, y * r = r * y) :
    y = 1 ∨ y = d.tau * d.z ∨ y = d.b ∨ y = d.tau * d.z * d.b := by
  obtain ⟨m, hm, hym⟩ := d.R_cases hy
  have hmc : ∀ r ∈ d.RM, m * r = r * m := by
    intro r hr
    have h1 := hc r (d.RM_le_R hr)
    have hrb := d.b_comm_of_mem_M3 (d.RM_le hr)
    rcases hym with rfl | rfl
    · exact h1
    · have h2 : m * r * d.b = r * m * d.b := by
        calc m * r * d.b = m * (r * d.b) := by group
          _ = m * (d.b * r) := by rw [hrb]
          _ = m * d.b * r := by group
          _ = r * (m * d.b) := h1
          _ = r * m * d.b := by group
      exact mul_right_cancel h2
  have hcen : (⟨d.rh m hm, d.rh_mem_cR hm⟩ : ↥d.c.R) ∈ center ↥d.c.R := by
    rw [mem_center_iff]
    rintro ⟨w, hw⟩
    have hw' := hw
    rw [d.c_R] at hw'
    obtain ⟨r, hr, rfl⟩ := mem_map.mp hw'
    apply Subtype.ext
    show H.rho r * d.rh m hm = d.rh m hm * H.rho r
    exact ((d.comm_iff hCF1 hCF2 hm hr).mp (hmc r hr)).symm
  have h1 : d.rh m hm ∈ (center d.c.R).map d.c.R.subtype := ⟨_, hcen, rfl⟩
  rw [d.c_props.Z_R] at h1
  have htz : d.tau * d.z ∈ d.RM := mul_mem d.tau_mem_RM d.z_mem_RM
  have hm' : m = 1 ∨ m = d.tau * d.z := by
    rcases mem_zpowers_two (d.orderOf_ctz hq hCF1 hCF2 hL0) h1 with h2 | h2
    · left
      refine d.rho_inj hCF1 hCF2 hm (one_mem _) ?_
      change d.rh m hm = d.rh 1 (one_mem _)
      rw [h2, d.rh_one]
    · right
      refine d.rho_inj hCF1 hCF2 hm htz ?_
      change d.rh m hm = d.rh (d.tau * d.z) htz
      rw [h2, d.rh_mul d.tau_mem_RM d.z_mem_RM, d.rh_tau, d.rh_z]
  rcases hm' with rfl | rfl <;> rcases hym with rfl | rfl
  · left; rfl
  · right; right; left; rw [one_mul]
  · right; left; rfl
  · right; right; right; rfl

theorem exists_v (hq : h.IsQ3) (hF : Cat8.Q3Facts) {U : Subgroup X} (hU : IsPGroup 2 U)
    (hRU : d.R ≤ U) (hne : d.R ≠ U) :
    ∃ v ∈ U, v ∉ d.R ∧ v ∈ normalizer (d.R : Set X) ∧ v ∈ normalizer (d.E : Set X) ∧
      v * d.b * v⁻¹ = d.tau * d.z * d.b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  obtain ⟨v, hvU, hvR, hvn⟩ := Eight.exists_mem_normalizer_not_mem hU hRU hne
  have hvN : v ∈ normalizer (d.R : Set X) := by
    have h1 := Eight.mem_normalizer_of_conj_mem (C := d.R) (s := v⁻¹) fun r hr => by
      rw [inv_inv]
      exact hvn r hr
    simpa using inv_mem h1
  have hvR' : ∀ r ∈ d.R, v⁻¹ * r * v ∈ d.R := fun r hr => by
    have := (mem_normalizer_iff.mp (inv_mem hvN) r).mp hr
    rwa [inv_inv] at this
  have hEv : conjugate d.E v⁻¹ = d.E := by
    have hmem : ∀ x, x ∈ conjugate d.E v⁻¹ ↔ v⁻¹ * x * v ∈ d.E := fun x => by
      rw [mem_conjugate_iff, inv_inv]
    refine d.eq_E_of_normal hq hF ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have h1 := d.E_le_R ((hmem x).mp hx)
      have h2 := hvn _ h1
      rwa [show v * (v⁻¹ * x * v) * v⁻¹ = x by group] at h2
    · intro x hx
      have h1 := d.E_sq hCF1 hCF2 ((hmem x).mp hx)
      calc x * x = v * ((v⁻¹ * x * v) * (v⁻¹ * x * v)) * v⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    · rw [Eight.card_conjugate_eq, d.card_E hCF1 hCF2]
    · intro r hr x hx
      rw [hmem] at hx ⊢
      have h1 := hvR' r hr
      have h2 := (mem_normalizer_iff.mp (d.R_le_normalizer_E h1) _).mp hx
      rwa [show v⁻¹ * r * v * (v⁻¹ * x * v) * (v⁻¹ * r * v)⁻¹ = v⁻¹ * (r * x * r⁻¹) * v by
        group] at h2
    · intro x hx g hg
      apply d.a_not_conj_E hq hF (g * v) ((hmem x).mp hx)
      rw [show (g * v)⁻¹ * h.a * (g * v) = v⁻¹ * (g⁻¹ * h.a * g) * v by group, hg]
  have hvE : v ∈ normalizer (d.E : Set X) :=
    by simpa using inv_mem (mem_normalizer_of_conjugate_eq hEv)
  refine ⟨v, hvU, hvR, hvN, hvE, ?_⟩
  have hbR : d.b ∈ d.R := mem_sup_right (d.B_eq ▸ mem_zpowers d.b)
  have hvb : v * d.b * v⁻¹ ∈ d.R := (mem_normalizer_iff.mp hvN d.b).mp hbR
  have hvbc : ∀ r ∈ d.R, v * d.b * v⁻¹ * r = r * (v * d.b * v⁻¹) := by
    intro r hr
    have h1 := mem_centralizer_singleton_iff.mp (d.R_le_centralizer_b (hvR' r hr))
    calc v * d.b * v⁻¹ * r = v * (d.b * (v⁻¹ * r * v)) * v⁻¹ := by group
      _ = v * ((v⁻¹ * r * v) * d.b) * v⁻¹ := by rw [h1]
      _ = r * (v * d.b * v⁻¹) := by group
  have hnf := d.not_fused hq hF
  rcases d.mem_center_R hq hCF1 hCF2 hF.l0 hvb hvbc with h1 | h1 | h1 | h1
  · exfalso
    have hb1 : d.b = 1 := by
      calc d.b = v⁻¹ * (v * d.b * v⁻¹) * v := by group
        _ = 1 := by rw [h1]; group
    have h2 := d.b_ord
    rw [hb1, orderOf_one] at h2
    norm_num at h2
  · exfalso
    apply (hnf v⁻¹).2.2.2.2.1
    rw [inv_inv]
    exact h1
  · exfalso
    have hvC : v ∈ centralizer ({d.b} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc v * d.b = v * d.b * v⁻¹ * v := by group
        _ = d.b * v := by rw [h1]
    have hle : zpowers v ≤ normalizer (d.R : Set X) := zpowers_le.mpr hvN
    have hp : IsPGroup 2 ↥(d.R ⊔ zpowers v) :=
      IsPGroup.to_sup_of_normal_left' (d.isPGroup_R hCF1 hCF2) (hU.to_le (zpowers_le.mpr hvU))
        hle
    have hC : d.R ⊔ zpowers v ≤ centralizer ({d.b} : Set X) :=
      sup_le d.R_le_centralizer_b (zpowers_le.mpr hvC)
    have hcard := d.card_le_of_le_centralizer_b hp hC
    have heq : d.R = d.R ⊔ zpowers v :=
      eq_of_le_of_card_ge le_sup_left (by rw [d.card_R hCF1 hCF2]; exact hcard)
    apply hvR
    rw [heq]
    exact mem_sup_right (mem_zpowers v)
  · exact h1

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
