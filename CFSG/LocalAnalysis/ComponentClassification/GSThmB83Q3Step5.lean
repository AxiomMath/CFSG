module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4e

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Cat8

theorem conj_mem_Inn {K₀ : Type} [Group K₀] (σ : MulAut K₀) {w : MulAut K₀}
    (hw : w ∈ Inn K₀) : σ * w * σ⁻¹ ∈ Inn K₀ := by
  obtain ⟨k, rfl⟩ := hw
  refine ⟨σ k, ?_⟩
  ext y
  simp [MulAut.conj_apply]

end Cat8

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

theorem rho_conj (H : L83Hyp h) {n u : X} (hn : n ∈ h.M3) (hu : u ∈ h.M3) :
    H.rho ⟨n⁻¹ * u * n, mul_mem (mul_mem (inv_mem hn) hu) hn⟩ =
      (H.rho ⟨n, hn⟩)⁻¹ * H.rho ⟨u, hu⟩ * H.rho ⟨n, hn⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

namespace Q3Data

variable (d : Q3Data H)
include d

noncomputable abbrev E0hat : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K)) :=
  d.c_props.E0.choose

noncomputable abbrev NE0hat : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K)) :=
  normalizer (d.E0hat : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K)))

theorem E0hat_le : d.E0hat ≤ d.c.R ⊓ Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) :=
  d.c_props.E0.choose_spec.1

theorem E0hat_sq : Cat8.IsElemAb2 d.E0hat := d.c_props.E0.choose_spec.2.1

theorem card_E0hat : Nat.card d.E0hat = 16 := d.c_props.E0.choose_spec.2.2.1

theorem E0hat_unique {E' : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K))}
    (h1 : E' ≤ d.c.R ⊓ Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K)) (h2 : Cat8.IsElemAb2 E')
    (h3 : Nat.card E' = 16) : E' = d.E0hat :=
  d.c_props.E0.choose_spec.2.2.2.1 E' h1 h2 h3

theorem cz_mem_E0hat : d.c.z ∈ d.E0hat := d.c_props.E0.choose_spec.2.2.2.2.1

theorem ctau_mem_E0hat : d.c.tau ∈ d.E0hat := d.c_props.E0.choose_spec.2.2.2.2.2.1

theorem centralizer_E0hat :
    centralizer (d.E0hat : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) = d.E0hat :=
  d.c_props.E0.choose_spec.2.2.2.2.2.2.1

theorem E0hat_cases {w : MulAut (h.K ⧸ pPrimeCore 2 h.K)} (hw : w ∈ d.E0hat) :
    w = 1 ∨ w ∈ Cat8.conjOrbit d.NE0hat d.c.z ∨
      w ∈ Cat8.conjOrbit d.NE0hat (d.c.z * d.c.tau) :=
  d.c_props.E0.choose_spec.2.2.2.2.2.2.2.1 w hw

theorem E0hat_card_cases :
    (Nat.card d.NE0hat = 1920 ∧ Nat.card (Cat8.conjOrbit d.NE0hat d.c.z) = 10 ∧
        Nat.card (Cat8.conjOrbit d.NE0hat (d.c.z * d.c.tau)) = 5 ∧
        closure (Cat8.conjOrbit d.NE0hat (d.c.z * d.c.tau)) = d.E0hat) ∨
      (Nat.card d.NE0hat = 1152 ∧ Nat.card (Cat8.conjOrbit d.NE0hat d.c.z) = 6 ∧
        Nat.card (Cat8.conjOrbit d.NE0hat (d.c.z * d.c.tau)) = 9 ∧
        closure {y | ∃ u ∈ Cat8.conjOrbit d.NE0hat d.c.z,
          ∃ v ∈ Cat8.conjOrbit d.NE0hat d.c.z, y = u * v} = d.E0hat) :=
  d.c_props.E0.choose_spec.2.2.2.2.2.2.2.2.1

theorem E0hat_normal {A : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K))} (h1 : A ≤ d.c.R)
    (h2 : Cat8.IsElemAb2 A) (h3 : Nat.card A = 16) (h4 : (A.subgroupOf d.c.R).Normal) :
    A = d.E0hat ∨ ∃ w ∈ A, ∃ y : MulAut (h.K ⧸ pPrimeCore 2 h.K), y⁻¹ * d.c.a * y = w :=
  d.c_props.E0.choose_spec.2.2.2.2.2.2.2.2.2.1 A h1 h2 h3 h4

theorem card_commutator_E0hat :
    Nat.card ↥(⁅d.E0hat, zpowers d.c.a⁆ : Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K))) = 2 :=
  d.c_props.E0.choose_spec.2.2.2.2.2.2.2.2.2.2.1

theorem exists_e_E0hat : ∃ e ∈ d.c.R ⊓ Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K),
    e ∈ ⁅d.NE0hat, d.NE0hat⁆ ∧ e * e = 1 ∧
      e ∉ centralizer (d.E0hat : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) :=
  d.c_props.E0.choose_spec.2.2.2.2.2.2.2.2.2.2.2

theorem conj_mem_E0hat {r w : MulAut (h.K ⧸ pPrimeCore 2 h.K)} (hr : r ∈ d.c.R)
    (hw : w ∈ d.E0hat) : r * w * r⁻¹ ∈ d.E0hat := by
  have hE : conjugate d.E0hat r⁻¹ = d.E0hat := by
    refine d.E0hat_unique ?_ ?_ ?_
    · intro x hx
      rw [mem_conjugate_iff, inv_inv] at hx
      have hx' := d.E0hat_le hx
      have hxR := (Subgroup.mem_inf.mp hx').1
      have hxI := (Subgroup.mem_inf.mp hx').2
      have hxe : x = r * (r⁻¹ * x * r) * r⁻¹ := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hxe]
        exact mul_mem (mul_mem hr hxR) (inv_mem hr)
      · rw [hxe]
        exact Cat8.conj_mem_Inn r hxI
    · intro x hx
      rw [mem_conjugate_iff, inv_inv] at hx
      have h1 := d.E0hat_sq _ hx
      calc x * x = r * ((r⁻¹ * x * r) * (r⁻¹ * x * r)) * r⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    · rw [Eight.card_conjugate_eq, d.card_E0hat]
  rw [← hE, mem_conjugate_iff, inv_inv]
  rwa [show r⁻¹ * (r * w * r⁻¹) * r = w by group]

noncomputable abbrev E0 : Subgroup X := d.RM ⊓ (d.E0hat.comap H.rho).map h.M3.subtype

theorem E0_le_RM : d.E0 ≤ d.RM := inf_le_left

theorem E0_le_M3 : d.E0 ≤ h.M3 := d.E0_le_RM.trans d.RM_le

theorem mem_E0_iff {x : X} (hx : x ∈ d.RM) : x ∈ d.E0 ↔ d.rh x hx ∈ d.E0hat := by
  constructor
  · intro h1
    obtain ⟨m, hm, hmx⟩ := mem_map.mp (Subgroup.mem_inf.mp h1).2
    subst hmx
    exact hm
  · intro h1
    exact Subgroup.mem_inf.mpr ⟨hx, mem_map.mpr ⟨⟨x, d.RM_le hx⟩, h1, rfl⟩⟩

theorem rh_mem_E0hat {x : X} (hx : x ∈ d.E0) : d.rh x (d.E0_le_RM hx) ∈ d.E0hat :=
  (d.mem_E0_iff (d.E0_le_RM hx)).mp hx

theorem isPGroup_E0 : IsPGroup 2 d.E0 := d.isPGroup_RM.to_le d.E0_le_RM

theorem E0_le_K (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : d.E0 ≤ h.K := fun x hx =>
  (H.mem_K_iff hCF1 hCF2 ⟨x, d.E0_le_M3 hx⟩).mpr (Subgroup.mem_inf.mp (d.E0hat_le
    (d.rh_mem_E0hat hx))).2

theorem map_E0 : (d.E0.subgroupOf h.M3).map H.rho = d.E0hat := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    exact d.rh_mem_E0hat hm
  · intro w hw
    have hwR : w ∈ d.c.R := (Subgroup.mem_inf.mp (d.E0hat_le hw)).1
    rw [d.c_R] at hwR
    obtain ⟨m, hm, rfl⟩ := mem_map.mp hwR
    exact mem_map.mpr ⟨m, (d.mem_E0_iff hm).mpr hw, rfl⟩

theorem exists_rh_E0 {w : MulAut (h.K ⧸ pPrimeCore 2 h.K)} (hw : w ∈ d.E0hat) :
    ∃ e : X, ∃ he : e ∈ d.E0, d.rh e (d.E0_le_RM he) = w := by
  rw [← d.map_E0] at hw
  obtain ⟨m, hm, rfl⟩ := mem_map.mp hw
  exact ⟨m, hm, rfl⟩

theorem card_E0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : Nat.card d.E0 = 16 := by
  have h2 : IsPGroup 2 (d.E0.subgroupOf h.M3) := d.isPGroup_E0.comap_subtype
  have h1 := Eight.card_map_of_isPGroup (H.not_two_dvd_card_ker_modelHom hCF1 hCF2) h2
  rw [d.map_E0, d.card_E0hat, ← card_map_of_injective h.M3.subtype_injective,
    map_subgroupOf_eq_of_le d.E0_le_M3] at h1
  exact h1.symm

theorem E0_sq (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {e : X} (he : e ∈ d.E0) :
    e * e = 1 := by
  have he' := d.E0_le_RM he
  refine d.rho_inj hCF1 hCF2 (mul_mem he' he') (one_mem _) ?_
  change d.rh (e * e) (mul_mem he' he') = d.rh 1 (one_mem _)
  rw [d.rh_mul he' he', d.rh_one]
  exact d.E0hat_sq _ (d.rh_mem_E0hat he)

theorem E0_comm (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {e f : X}
    (he : e ∈ d.E0) (hf : f ∈ d.E0) : e * f = f * e :=
  Eight.comm_of_mul_self (fun _ hy => d.E0_sq hCF1 hCF2 hy) he hf

theorem z_mem_E0 : d.z ∈ d.E0 :=
  (d.mem_E0_iff d.z_mem_RM).mpr (by rw [d.rh_z]; exact d.cz_mem_E0hat)

theorem tau_mem_E0 : d.tau ∈ d.E0 :=
  (d.mem_E0_iff d.tau_mem_RM).mpr (by rw [d.rh_tau]; exact d.ctau_mem_E0hat)

theorem RM_le_normalizer_E0 : d.RM ≤ normalizer (d.E0 : Set X) := by
  apply le_normalizer_of_conj
  intro r hr e he
  have he' := d.E0_le_RM he
  have hrer : r * e * r⁻¹ ∈ d.RM := mul_mem (mul_mem hr he') (inv_mem hr)
  refine (d.mem_E0_iff hrer).mpr ?_
  have h1 : d.rh (r * e * r⁻¹) hrer = d.rh r hr * d.rh e he' * (d.rh r hr)⁻¹ := by
    rw [d.rh_mul (mul_mem hr he') (inv_mem hr), d.rh_mul hr he', d.rh_inv hr]
  rw [h1]
  refine d.conj_mem_E0hat ?_ (d.rh_mem_E0hat he)
  rw [d.c_R]
  exact mem_map_of_mem H.rho (show (⟨r, d.RM_le hr⟩ : ↥h.M3) ∈ d.RM.subgroupOf h.M3 from hr)

noncomputable abbrev E : Subgroup X := d.E0 ⊔ h.B

theorem E0_le_E : d.E0 ≤ d.E := le_sup_left

theorem b_mem_E : d.b ∈ d.E := mem_sup_right (d.B_eq ▸ mem_zpowers d.b)

theorem b_comm_E0 {e : X} (he : e ∈ d.E0) : e * d.b = d.b * e :=
  d.b_comm_of_mem_M3 (d.E0_le_M3 he)

theorem b_mem_normalizer_E0 : d.b ∈ normalizer (d.E0 : Set X) :=
  centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ he => d.b_comm_E0 he)

theorem mem_E_cases {y : X} (hy : y ∈ d.E) : ∃ e ∈ d.E0, y = e ∨ y = e * d.b := by
  have hy' : y ∈ d.E0 ⊔ zpowers d.b := by
    rw [← d.B_eq]
    exact hy
  exact Eight.mem_sup_zpowers_cases d.b_mem_normalizer_E0 d.b_mul_self hy'

theorem E_sq (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y : X} (hy : y ∈ d.E) :
    y * y = 1 := by
  obtain ⟨e, he, rfl | rfl⟩ := d.mem_E_cases hy
  · exact d.E0_sq hCF1 hCF2 he
  · calc e * d.b * (e * d.b) = e * (d.b * e) * d.b := by group
      _ = e * (e * d.b) * d.b := by rw [d.b_comm_E0 he]
      _ = (e * e) * (d.b * d.b) := by group
      _ = 1 := by rw [d.E0_sq hCF1 hCF2 he, d.b_mul_self, one_mul]

theorem E_comm (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y y' : X} (hy : y ∈ d.E)
    (hy' : y' ∈ d.E) : y * y' = y' * y :=
  Eight.comm_of_mul_self (fun _ hw => d.E_sq hCF1 hCF2 hw) hy hy'

theorem card_E (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : Nat.card d.E = 32 := by
  rw [d.card_sup_B hCF1 hCF2 d.E0_le_M3, d.card_E0 hCF1 hCF2]

theorem isPGroup_E (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : IsPGroup 2 d.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 5) (by rw [d.card_E hCF1 hCF2]; norm_num)

theorem E_le_R : d.E ≤ d.R := sup_le (d.E0_le_RM.trans le_sup_left) le_sup_right

theorem le_normalizer_E :
    normalizer (d.E0 : Set X) ⊓ centralizer ({d.b} : Set X) ≤ normalizer (d.E : Set X) := by
  apply le_normalizer_of_conj
  intro y hy w hw
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
  have hyb : y * d.b * y⁻¹ = d.b := by
    rw [mem_centralizer_singleton_iff.mp hy2, mul_inv_cancel_right]
  have hyE0 : ∀ e ∈ d.E0, y * e * y⁻¹ ∈ d.E := fun e he =>
    d.E0_le_E ((mem_normalizer_iff.mp hy1 e).mp he)
  obtain ⟨e, he, h1 | h1⟩ := d.mem_E_cases hw
  · rw [h1]
    exact hyE0 e he
  · rw [h1, show y * (e * d.b) * y⁻¹ = (y * e * y⁻¹) * (y * d.b * y⁻¹) by group, hyb]
    exact mul_mem (hyE0 e he) d.b_mem_E

theorem R_le_normalizer_E : d.R ≤ normalizer (d.E : Set X) := by
  refine le_trans ?_ d.le_normalizer_E
  refine sup_le (le_inf d.RM_le_normalizer_E0 (d.RM_le.trans d.M3_le_centralizer_b)) ?_
  rw [d.B_eq, zpowers_le]
  exact Subgroup.mem_inf.mpr ⟨d.b_mem_normalizer_E0, mem_centralizer_singleton_iff.mpr rfl⟩

theorem oddBar_comm_E0 {t : X} (ht : t ∈ normalizer (h.K : Set X)) {e : X} (he : e ∈ d.E0)
    (hte : t * e = e * t) :
    Eight.oddBarAction h.K ⟨t, ht⟩ * d.rh e (d.E0_le_RM he) =
      d.rh e (d.E0_le_RM he) * Eight.oddBarAction h.K ⟨t, ht⟩ := by
  have heN : e ∈ normalizer (h.K : Set X) :=
    Eight.sup_zpowers_le_normalizer H.a_mem_normalizer_K (d.E0_le_M3 he)
  have hre : d.rh e (d.E0_le_RM he) = Eight.oddBarAction h.K ⟨e, heN⟩ := rfl
  rw [hre, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hte

theorem card_le_of_comm_E0 {A : Subgroup X} (hA : IsPGroup 2 A)
    (hAb : A ≤ centralizer ({d.b} : Set X)) (hAE : ∀ t ∈ A, ∀ e ∈ d.E0, t * e = e * t) :
    Nat.card A ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : A ≤ normalizer (h.K : Set X) := hAb.trans d.centralizer_b_le
  let φ : A →* MulAut (h.K ⧸ pPrimeCore 2 h.K) := (Eight.oddBarAction h.K).comp (inclusion hAN)
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range ≤ 16 := by
    have hle : φ.range ≤ d.E0hat := by
      rintro _ ⟨t, rfl⟩
      rw [← d.centralizer_E0hat, mem_centralizer_iff]
      intro w hw
      obtain ⟨e, he, rfl⟩ := d.exists_rh_E0 hw
      exact (d.oddBar_comm_E0 (hAN t.2) he (hAE t t.2 e he)).symm
    rw [← d.card_E0hat]
    exact card_le_of_le hle
  have hker : Nat.card φ.ker ≤ 2 := by
    have hk : φ.ker.map A.subtype ≤ coreActionKernel h.V := by
      rintro _ ⟨y, hy, rfl⟩
      rw [H.V_eq_K]
      exact Eight.mem_ker_oddBarAction.mp hy
    have h2 := card_le_of_sylow_subgroupOf H.B_sylow_kernel.2 hk
      ((hA.to_subgroup φ.ker).map A.subtype)
    rw [card_map_of_injective A.subtype_injective, d.card_B] at h2
    exact h2
  have h3 : Nat.card A ≤ 2 * 16 := by
    rw [← h1]
    exact Nat.mul_le_mul hker hrange
  omega

theorem mem_E_of_comm (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {k : X}
    (hk : IsPGroup 2 (zpowers k)) (hkE : ∀ e ∈ d.E, k * e = e * k) : k ∈ d.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkC : k ∈ centralizer (d.E : Set X) := mem_centralizer_iff.mpr fun e he => (hkE e he).symm
  have hkN : zpowers k ≤ normalizer (d.E : Set X) := by
    rw [zpowers_le]
    exact centralizer_le_normalizer _ hkC
  have hA : IsPGroup 2 ↥(d.E ⊔ zpowers k) :=
    IsPGroup.to_sup_of_normal_left' (d.isPGroup_E hCF1 hCF2) hk hkN
  have hAc : d.E ⊔ zpowers k ≤ centralizer (d.E : Set X) := by
    refine sup_le (fun y hy => mem_centralizer_iff.mpr fun e he => d.E_comm hCF1 hCF2 he hy) ?_
    rw [zpowers_le]
    exact hkC
  have hcard := d.card_le_of_comm_E0 hA
    (hAc.trans (centralizer_le (Set.singleton_subset_iff.mpr d.b_mem_E)))
    (fun t ht e he => (mem_centralizer_iff.mp (hAc ht) e (d.E0_le_E he)).symm)
  have heq : d.E = d.E ⊔ zpowers k :=
    eq_of_le_of_card_ge le_sup_left (by rw [d.card_E hCF1 hCF2]; exact hcard)
  rw [heq]
  exact mem_sup_right (mem_zpowers k)

theorem mem_E_of_comm_of_mem (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    {T : Subgroup X} (hT : IsPGroup 2 T) {k : X} (hkT : k ∈ T)
    (hkE : ∀ e ∈ d.E, k * e = e * k) : k ∈ d.E :=
  d.mem_E_of_comm hCF1 hCF2 (hT.to_le (zpowers_le.mpr hkT)) hkE

noncomputable abbrev NME0 : Subgroup X := h.M3 ⊓ normalizer (d.E0 : Set X)

theorem NME0_le_normalizer_E : d.NME0 ≤ normalizer (d.E : Set X) :=
  (le_inf inf_le_right (inf_le_left.trans d.M3_le_centralizer_b)).trans d.le_normalizer_E

theorem NME0_le_centralizer_b : d.NME0 ≤ centralizer ({d.b} : Set X) :=
  inf_le_left.trans d.M3_le_centralizer_b

theorem rho_mem_NE0hat {n : X} (hn : n ∈ d.NME0) :
    H.rho ⟨n, (Subgroup.mem_inf.mp hn).1⟩ ∈ d.NE0hat := by
  have h1 : (⟨n, (Subgroup.mem_inf.mp hn).1⟩ : ↥h.M3) ∈
      normalizer ((d.E0.subgroupOf h.M3 : Subgroup ↥h.M3) : Set ↥h.M3) := by
    rw [← subgroupOf_normalizer_eq d.E0_le_M3]
    exact (Subgroup.mem_inf.mp hn).2
  have h2 := le_normalizer_map H.rho (mem_map_of_mem H.rho h1)
  rw [d.map_E0] at h2
  exact h2

theorem exists_lift_NE0hat (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) {w : MulAut (h.K ⧸ pPrimeCore 2 h.K)} (hw : w ∈ d.NE0hat) :
    ∃ n : X, ∃ hn : n ∈ d.NME0, H.rho ⟨n, (Subgroup.mem_inf.mp hn).1⟩ = w := by
  have h1 : (normalizer ((d.E0.subgroupOf h.M3 : Subgroup ↥h.M3) : Set ↥h.M3)).map H.rho =
      H.rho.range ⊓ normalizer (((d.E0.subgroupOf h.M3).map H.rho :
        Subgroup (MulAut (h.K ⧸ pPrimeCore 2 h.K))) : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) :=
    Eight.map_normalizer_eq (H.not_two_dvd_card_ker_modelHom hCF1 hCF2)
      d.isPGroup_E0.comap_subtype
  rw [d.map_E0, H.rho_range hq hCF1 hCF2 hOut, top_inf_eq,
    ← subgroupOf_normalizer_eq d.E0_le_M3] at h1
  have hw' : w ∈ normalizer (d.E0hat : Set (MulAut (h.K ⧸ pPrimeCore 2 h.K))) := hw
  rw [← h1] at hw'
  obtain ⟨m, hm, rfl⟩ := mem_map.mp hw'
  exact ⟨m, Subgroup.mem_inf.mpr ⟨m.2, hm⟩, rfl⟩

theorem conj_mem_E0 {n e : X} (hn : n ∈ d.NME0) (he : e ∈ d.E0) : n⁻¹ * e * n ∈ d.E0 := by
  have := (mem_normalizer_iff.mp (inv_mem (Subgroup.mem_inf.mp hn).2) e).mp he
  rwa [inv_inv] at this

theorem conj_eq_iff (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {n u e : X}
    (hn : n ∈ d.NME0) (hu : u ∈ d.E0) (he : e ∈ d.E0) :
    n⁻¹ * u * n = e ↔ (H.rho ⟨n, (Subgroup.mem_inf.mp hn).1⟩)⁻¹ * d.rh u (d.E0_le_RM hu) *
      H.rho ⟨n, (Subgroup.mem_inf.mp hn).1⟩ = d.rh e (d.E0_le_RM he) := by
  have hc := d.conj_mem_E0 hn hu
  have key : d.rh (n⁻¹ * u * n) (d.E0_le_RM hc) = (H.rho ⟨n, (Subgroup.mem_inf.mp hn).1⟩)⁻¹ *
      d.rh u (d.E0_le_RM hu) * H.rho ⟨n, (Subgroup.mem_inf.mp hn).1⟩ :=
    H.rho_conj (Subgroup.mem_inf.mp hn).1 (d.E0_le_M3 hu)
  rw [← key]
  constructor
  · intro h1
    subst h1
    rfl
  · intro h1
    exact d.rho_inj hCF1 hCF2 (d.E0_le_RM hc) (d.E0_le_RM he) h1

theorem E0_cases (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) {e : X} (he : e ∈ d.E0) :
    e = 1 ∨ (∃ n ∈ d.NME0, n⁻¹ * d.z * n = e) ∨
      ∃ n ∈ d.NME0, n⁻¹ * (d.z * d.tau) * n = e := by
  have hzt : d.z * d.tau ∈ d.E0 := mul_mem d.z_mem_E0 d.tau_mem_E0
  have hrzt : d.rh (d.z * d.tau) (d.E0_le_RM hzt) = d.c.z * d.c.tau := by
    rw [d.rh_mul d.z_mem_RM d.tau_mem_RM, d.rh_z, d.rh_tau]
  rcases d.E0hat_cases (d.rh_mem_E0hat he) with h1 | ⟨w, hw, hwe⟩ | ⟨w, hw, hwe⟩
  · left
    refine d.rho_inj hCF1 hCF2 (d.E0_le_RM he) (one_mem _) ?_
    change d.rh e (d.E0_le_RM he) = d.rh 1 (one_mem _)
    rw [h1, d.rh_one]
  · right; left
    obtain ⟨n, hn, rfl⟩ := d.exists_lift_NE0hat hq hCF1 hCF2 hOut hw
    refine ⟨n, hn, (d.conj_eq_iff hCF1 hCF2 hn d.z_mem_E0 he).mpr ?_⟩
    rw [d.rh_z]
    exact hwe
  · right; right
    obtain ⟨n, hn, rfl⟩ := d.exists_lift_NE0hat hq hCF1 hCF2 hOut hw
    refine ⟨n, hn, (d.conj_eq_iff hCF1 hCF2 hn hzt he).mpr ?_⟩
    rw [hrzt]
    exact hwe

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
