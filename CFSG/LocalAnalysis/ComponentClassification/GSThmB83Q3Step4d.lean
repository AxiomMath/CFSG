module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Dihedral
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4

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

abbrev R0M : Subgroup X := d.RM ⊓ centralizer ({d.z} : Set X)

noncomputable abbrev rh (y : X) (hy : y ∈ d.RM) : MulAut (h.K ⧸ pPrimeCore 2 h.K) :=
  H.rho ⟨y, d.RM_le hy⟩

theorem rh_mul {u v : X} (hu : u ∈ d.RM) (hv : v ∈ d.RM) :
    d.rh (u * v) (mul_mem hu hv) = d.rh u hu * d.rh v hv := by
  rw [← map_mul]
  rfl

theorem rh_inv {u : X} (hu : u ∈ d.RM) : d.rh u⁻¹ (inv_mem hu) = (d.rh u hu)⁻¹ := by
  rw [← map_inv]
  rfl

theorem rh_one : d.rh 1 (one_mem _) = 1 := map_one _

theorem rh_z (hz : d.z ∈ d.RM) : d.rh d.z hz = d.c.z := d.c_z.symm

theorem rh_tau (ht : d.tau ∈ d.RM) : d.rh d.tau ht = d.c.tau := d.rho_tau

theorem rh_mem_R0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y : X}
    (hy : y ∈ d.R0M) : d.rh y hy.1 ∈ d.c.R0 := by
  rw [← d.map_RM_inf_centralizer_z hCF1 hCF2]
  exact mem_map_of_mem _ hy

theorem exists_rh_eq (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    {w : MulAut (h.K ⧸ pPrimeCore 2 h.K)} (hw : w ∈ d.c.R0) :
    ∃ y : X, ∃ hy : y ∈ d.R0M, d.rh y hy.1 = w := by
  rw [← d.map_RM_inf_centralizer_z hCF1 hCF2] at hw
  obtain ⟨m, hm, rfl⟩ := mem_map.mp hw
  exact ⟨m, hm, rfl⟩

theorem comm_iff (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {u v : X}
    (hu : u ∈ d.RM) (hv : v ∈ d.RM) :
    u * v = v * u ↔ d.rh u hu * d.rh v hv = d.rh v hv * d.rh u hu := by
  rw [← d.rh_mul, ← d.rh_mul]
  constructor
  · intro h1
    simp only [rh]
    congr 1
    exact Subtype.ext h1
  · exact d.rho_inj hCF1 hCF2 (mul_mem hu hv) (mul_mem hv hu)

theorem central_iff (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y : X}
    (hy : y ∈ d.R0M) :
    (∀ r ∈ d.R0M, y * r = r * y) ↔ ∀ w ∈ d.c.R0, d.rh y hy.1 * w = w * d.rh y hy.1 := by
  constructor
  · intro h1 w hw
    obtain ⟨r, hr, rfl⟩ := d.exists_rh_eq hCF1 hCF2 hw
    exact (d.comm_iff hCF1 hCF2 hy.1 hr.1).mp (h1 r hr)
  · intro h1 r hr
    exact (d.comm_iff hCF1 hCF2 hy.1 hr.1).mpr (h1 _ (d.rh_mem_R0 hCF1 hCF2 hr))

theorem z_mem_R0M : d.z ∈ d.R0M := ⟨d.z_mem_RM, mem_centralizer_singleton_iff.mpr rfl⟩

theorem tau_mem_RM : d.tau ∈ d.RM := d.Q1_le_RM d.tau_mem

theorem orderOf_cz : orderOf d.c.z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact d.c.z_sq) d.c.z_ne

theorem mem_center_R0M (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y : X}
    (hy : y ∈ d.R0M) (hc : ∀ r ∈ d.R0M, y * r = r * y) :
    y = 1 ∨ y = d.z ∨ y = d.tau ∨ y = d.tau * d.z := by
  have hzR := d.z_mem_RM
  have htR := d.tau_mem_RM
  have hcen : (⟨d.rh y hy.1, d.rh_mem_R0 hCF1 hCF2 hy⟩ : ↥d.c.R0) ∈ center ↥d.c.R0 := by
    rw [mem_center_iff]
    intro w
    exact Subtype.ext ((d.central_iff hCF1 hCF2 hy).mp hc w w.2).symm
  have h1 : d.rh y hy.1 ∈ (center d.c.R0).map d.c.R0.subtype := ⟨_, hcen, rfl⟩
  rw [d.c_props.R0_center.1] at h1
  have hzt : d.c.tau * d.c.z = d.c.z * d.c.tau := by
    rw [← d.rh_z hzR, ← d.rh_tau htR]
    exact (d.comm_iff hCF1 hCF2 htR hzR).mp (d.tau_comm_z hCF1 hCF2)
  have ht2 : d.c.tau * d.c.tau = 1 := by
    rw [← d.rh_tau htR, ← d.rh_mul, ← d.rh_one]
    simp only [rh]
    congr 1
    exact Subtype.ext d.tau_sq
  have htN : d.c.tau ∈ normalizer ((zpowers d.c.z : Subgroup _) : Set (MulAut _)) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw => ?_)
    rcases mem_zpowers_two d.orderOf_cz hw with rfl | rfl
    · simp
    · exact hzt.symm
  obtain ⟨m, hm, hym⟩ := Eight.mem_sup_zpowers_cases htN ht2 h1
  have key : ∀ u (hu : u ∈ d.RM), d.rh y hy.1 = d.rh u hu → y = u := fun u hu huv =>
    d.rho_inj hCF1 hCF2 hy.1 hu huv
  rcases mem_zpowers_two d.orderOf_cz hm with rfl | rfl <;> rcases hym with hym | hym
  · left
    exact key 1 (one_mem _) (by rw [hym, d.rh_one])
  · right; right; left
    exact key _ htR (by rw [hym, one_mul, d.rh_tau])
  · right; left
    exact key _ hzR (by rw [hym, d.rh_z])
  · right; right; right
    refine key _ (mul_mem htR hzR) ?_
    rw [hym, d.rh_mul htR hzR, d.rh_tau, d.rh_z, hzt]

theorem R0M_le_closure (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    d.R0M ≤ closure {y | ∃ A : Subgroup X, A ≤ d.R0M ∧ (∀ u ∈ A, u * u = 1) ∧
      Nat.card A = 16 ∧ y ∈ A} := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  set S := {y | ∃ A : Subgroup X, A ≤ d.R0M ∧ (∀ u ∈ A, u * u = 1) ∧ Nat.card A = 16 ∧ y ∈ A}
    with hS
  have hSR : closure S ≤ d.R0M := (closure_le _).mpr fun y hy => by
    obtain ⟨A, hA, -, -, hy⟩ := hy
    exact hA hy
  have hlift : ∀ Â : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K)), Â ≤ d.c.R0 →
      Cat8.IsElemAb2 Â → Nat.card Â = 16 → ∀ w ∈ Â, ∃ y : X, ∃ hy : y ∈ d.R0M, y ∈ S ∧
        d.rh y hy.1 = w := by
    intro Â hÂ hÂ2 hÂc w hw
    let A : Subgroup X := (Â.comap H.rho).map h.M3.subtype ⊓ d.R0M
    have hAR : A ≤ d.R0M := inf_le_right
    have hmemA : ∀ y (hy : y ∈ d.R0M), d.rh y hy.1 ∈ Â → y ∈ A := fun y hy h1 =>
      ⟨⟨⟨y, d.RM_le hy.1⟩, h1, rfl⟩, hy⟩
    have hrhA : ∀ y (hy : y ∈ A), d.rh y (hAR hy).1 ∈ Â := by
      rintro _ ⟨⟨m, hm, rfl⟩, hy⟩
      exact hm
    have hmap : (A.subgroupOf h.M3).map H.rho = Â := by
      apply le_antisymm
      · rintro _ ⟨m, hm, rfl⟩
        exact hrhA m hm
      · intro w' hw'
        obtain ⟨y, hy, rfl⟩ := d.exists_rh_eq hCF1 hCF2 (hÂ hw')
        exact mem_map_of_mem _ (hmemA y hy hw')
    have hA2 : IsPGroup 2 (A.subgroupOf h.M3) :=
      (d.isPGroup_RM.to_le (hAR.trans inf_le_left)).comap_subtype
    have hcard : Nat.card A = 16 := by
      rw [← hÂc, ← hmap, Eight.card_map_of_isPGroup hker hA2,
        ← card_map_of_injective h.M3.subtype_injective,
        map_subgroupOf_eq_of_le (hAR.trans (inf_le_left.trans d.RM_le))]
    have hAe : ∀ u ∈ A, u * u = 1 := by
      intro u hu
      have hu' := hrhA u hu
      have h1 := hÂ2 _ hu'
      have hR := (hAR hu).1
      refine d.rho_inj hCF1 hCF2 (mul_mem hR hR) (one_mem _) ?_
      rw [show H.rho ⟨u * u, d.RM_le (mul_mem hR hR)⟩ = d.rh u hR * d.rh u hR from
        d.rh_mul hR hR, h1]
      exact (map_one _).symm
    obtain ⟨y, hy, rfl⟩ := d.exists_rh_eq hCF1 hCF2 (hÂ hw)
    exact ⟨y, hy, ⟨A, hAR, hAe, hcard, hmemA y hy hw⟩, rfl⟩
  intro y hy
  have h1 := d.rh_mem_R0 hCF1 hCF2 hy
  rw [← d.c_props.R0_gen] at h1
  have h2 : closure {w | ∃ Â : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K)), Â ≤ d.c.R0 ∧
      Cat8.IsElemAb2 Â ∧ Nat.card Â = 16 ∧ w ∈ Â} ≤ ((closure S).subgroupOf h.M3).map H.rho := by
    rw [closure_le]
    rintro w ⟨Â, hÂ, hÂ2, hÂc, hw⟩
    obtain ⟨y', hy', hyS, rfl⟩ := hlift Â hÂ hÂ2 hÂc w hw
    exact mem_map_of_mem _ (subset_closure hyS)
  obtain ⟨m, hm, hmy⟩ := mem_map.mp (h2 h1)
  have hmR : (m : X) ∈ d.RM := (hSR hm).1
  have := d.rho_inj hCF1 hCF2 hmR hy.1 hmy
  rw [← this]
  exact hm

theorem exists_noncentral_comm_z (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    {A : Subgroup X} (hA : A ≤ d.R0M) (hA2 : ∀ u ∈ A, u * u = 1) (hA8 : 8 ≤ Nat.card A)
    (hAZ : ∀ u ∈ A, (∀ r ∈ d.R0M, u * r = r * u) → u = 1 ∨ u = d.tau * d.z) :
    ∃ y ∈ A, (∃ r ∈ d.R0M, y * r ≠ r * y) ∧
      ∀ r ∈ d.R0M, y⁻¹ * r⁻¹ * y * r = 1 ∨ y⁻¹ * r⁻¹ * y * r = d.z := by
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hzR := d.z_mem_RM
  have htR := d.tau_mem_RM
  obtain ⟨D₁, D₂, hD12, hD, hc, ⟨e₁⟩, ⟨e₂⟩, hz₁, -⟩ := d.c_props.R0_decomp
  have hAM : A ≤ h.M3 := hA.trans (inf_le_left.trans d.RM_le)
  set Â := (A.subgroupOf h.M3).map H.rho with hÂdef
  have hmemÂ : ∀ y (hy : y ∈ A), d.rh y (hA hy).1 ∈ Â := fun y hy => mem_map_of_mem _ hy
  have hÂA : ∀ w ∈ Â, ∃ y : X, ∃ hy : y ∈ A, d.rh y (hA hy).1 = w := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := mem_map.mp hw
    exact ⟨m, hm, rfl⟩
  have hA2' : IsPGroup 2 (A.subgroupOf h.M3) :=
    (d.isPGroup_RM.to_le (hA.trans inf_le_left)).comap_subtype
  have hÂR : Â ≤ D₁ ⊔ D₂ := by
    rw [hD12]
    intro w hw
    obtain ⟨y, hy, rfl⟩ := hÂA w hw
    exact d.rh_mem_R0 hCF1 hCF2 (hA hy)
  have hÂ2 : ∀ w ∈ Â, w * w = 1 := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := hÂA w hw
    rw [← d.rh_mul, ← d.rh_one]
    simp only [rh]
    congr 1
    exact Subtype.ext (hA2 y hy)
  have hÂ8 : 8 ≤ Nat.card Â := by
    rw [hÂdef, Eight.card_map_of_isPGroup hker hA2', ← card_map_of_injective h.M3.subtype_injective,
      map_subgroupOf_eq_of_le hAM]
    exact hA8
  have hÂZ : ∀ w ∈ Â, (∀ r ∈ D₁ ⊔ D₂, w * r = r * w) → w = 1 ∨ w = d.c.tau * d.c.z := by
    intro w hw hwc
    obtain ⟨y, hy, rfl⟩ := hÂA w hw
    rw [hD12] at hwc
    rcases hAZ y hy ((d.central_iff hCF1 hCF2 (hA hy)).mpr hwc) with rfl | rfl
    · left
      exact d.rh_one
    · right
      rw [d.rh_mul htR hzR, d.rh_tau, d.rh_z]
  obtain ⟨w, hw, ⟨t, ht, hwr⟩, hcomm⟩ :=
    Eight.exists_noncentral_commutator_le hD hc e₁ e₂ hz₁ hÂR hÂ2 hÂ8 hÂZ
  obtain ⟨y, hy, rfl⟩ := hÂA w hw
  refine ⟨y, hy, ?_, fun r hr => ?_⟩
  · by_contra hall
    push Not at hall
    rw [hD12] at ht
    exact hwr ((d.central_iff hCF1 hCF2 (hA hy)).mp hall t ht)
  · have hyR := (hA hy).1
    have h1 := hcomm _ (hD12 ▸ d.rh_mem_R0 hCF1 hCF2 hr)
    have hk : y⁻¹ * r⁻¹ * y * r ∈ d.RM :=
      mul_mem (mul_mem (mul_mem (inv_mem hyR) (inv_mem hr.1)) hyR) hr.1
    have h2 : d.rh (y⁻¹ * r⁻¹ * y * r) hk =
        (d.rh y hyR)⁻¹ * (d.rh r hr.1)⁻¹ * d.rh y hyR * d.rh r hr.1 := by
      rw [d.rh_mul (mul_mem (mul_mem (inv_mem hyR) (inv_mem hr.1)) hyR) hr.1,
        d.rh_mul (mul_mem (inv_mem hyR) (inv_mem hr.1)) hyR,
        d.rh_mul (inv_mem hyR) (inv_mem hr.1), d.rh_inv, d.rh_inv]
    rcases mem_zpowers_two d.orderOf_cz h1 with h3 | h3
    · left
      refine d.rho_inj hCF1 hCF2 hk (one_mem _) ?_
      rw [show H.rho ⟨y⁻¹ * r⁻¹ * y * r, d.RM_le hk⟩ = d.rh _ hk from rfl, h2, h3]
      exact (map_one _).symm
    · right
      refine d.rho_inj hCF1 hCF2 hk hzR ?_
      rw [show H.rho ⟨y⁻¹ * r⁻¹ * y * r, d.RM_le hk⟩ = d.rh _ hk from rfl, h2, h3]
      exact (d.rh_z hzR).symm

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
