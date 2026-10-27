module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step5b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Eight

theorem card_mul_relIndex_of_le {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  rw [Subgroup.relIndex, ← card_mul_index (H.subgroupOf K)]
  congr 1
  rw [← card_map_of_injective K.subtype_injective, map_subgroupOf_eq_of_le hHK]

end Eight

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace Q3Data

variable (d : Q3Data H)
include d

noncomputable abbrev NE : Subgroup X := normalizer (d.E : Set X)

noncomputable abbrev CNE : Subgroup X := d.NE ⊓ centralizer (d.E : Set X)

noncomputable abbrev CME0 : Subgroup X := h.M3 ⊓ centralizer (d.E0 : Set X)

theorem CME0_le_NME0 : d.CME0 ≤ d.NME0 := fun _ hx =>
  Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
    centralizer_le_normalizer _ (Subgroup.mem_inf.mp hx).2⟩

theorem comm_E_of_comm {x : X} (h0 : ∀ e ∈ d.E0, e * x = x * e) (hb : d.b * x = x * d.b) :
    ∀ e ∈ d.E, e * x = x * e := by
  intro e he
  obtain ⟨e', he', hee | hee⟩ := d.mem_E_cases he
  · rw [hee]
    exact h0 e' he'
  · rw [hee]
    calc e' * d.b * x = e' * (d.b * x) := by group
      _ = e' * (x * d.b) := by rw [hb]
      _ = e' * x * d.b := by group
      _ = x * e' * d.b := by rw [h0 e' he']
      _ = x * (e' * d.b) := by group

theorem CNE_inf_NME0 : d.CNE ⊓ d.NME0 = d.CME0 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h2).1, ?_⟩
    rw [mem_centralizer_iff]
    intro e he
    exact mem_centralizer_iff.mp (Subgroup.mem_inf.mp h1).2 e (d.E0_le_E he)
  · intro x hx
    have hxN := d.CME0_le_NME0 hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨d.NME0_le_normalizer_E hxN, ?_⟩, hxN⟩
    rw [mem_centralizer_iff]
    refine d.comm_E_of_comm (mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2) ?_
    exact (mem_centralizer_singleton_iff.mp (d.M3_le_centralizer_b (Subgroup.mem_inf.mp hx).1)).symm

theorem card_NME0_mul (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) : Nat.card d.NME0 * 16 = Nat.card d.NE0hat * Nat.card d.CME0 := by
  have hNM : d.NME0 ≤ h.M3 := inf_le_left
  have hCM : d.CME0 ≤ h.M3 := inf_le_left
  let φN : ↥d.NME0 →* MulAut (h.K ⧸ pPrimeCore 2 h.K) := H.rho.comp (inclusion hNM)
  let φC : ↥d.CME0 →* MulAut (h.K ⧸ pPrimeCore 2 h.K) := H.rho.comp (inclusion hCM)
  have h1 := Subgroup.card_ker_mul_card_range φN
  have h2 := Subgroup.card_ker_mul_card_range φC
  have hrN : φN.range = d.NE0hat := by
    apply le_antisymm
    · rintro _ ⟨n, rfl⟩
      exact d.rho_mem_NE0hat n.2
    · intro w hw
      obtain ⟨n, hn, rfl⟩ := d.exists_lift_NE0hat hq hCF1 hCF2 hOut hw
      exact ⟨⟨n, hn⟩, rfl⟩
  have hrC : φC.range = d.E0hat := by
    apply le_antisymm
    · rintro _ ⟨n, rfl⟩
      rw [← d.centralizer_E0hat, mem_centralizer_iff]
      intro w hw
      obtain ⟨e, he, rfl⟩ := d.exists_rh_E0 hw
      have hne : e * (n : X) = (n : X) * e :=
        mem_centralizer_iff.mp (Subgroup.mem_inf.mp n.2).2 e he
      show H.rho ⟨e, d.RM_le (d.E0_le_RM he)⟩ * H.rho ⟨n, hCM n.2⟩ =
        H.rho ⟨n, hCM n.2⟩ * H.rho ⟨e, d.RM_le (d.E0_le_RM he)⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hne
    · intro w hw
      obtain ⟨e, he, rfl⟩ := d.exists_rh_E0 hw
      refine ⟨⟨e, Subgroup.mem_inf.mpr ⟨d.E0_le_M3 he, mem_centralizer_iff.mpr fun f hf =>
        d.E0_comm hCF1 hCF2 hf he⟩⟩, rfl⟩
  have hkereq : φN.ker.map d.NME0.subtype = φC.ker.map d.CME0.subtype := by
    apply le_antisymm
    · rintro _ ⟨n, hn, rfl⟩
      have hn1 : H.rho ⟨n, hNM n.2⟩ = 1 := hn
      have hnC : (n : X) ∈ d.CME0 := by
        refine Subgroup.mem_inf.mpr ⟨hNM n.2, mem_centralizer_iff.mpr fun e he => ?_⟩
        have h3 : (n : X) * e * (n : X)⁻¹ ∈ d.E0 :=
          (mem_normalizer_iff.mp (Subgroup.mem_inf.mp n.2).2 e).mp he
        have h4 : d.rh ((n : X) * e * (n : X)⁻¹) (d.E0_le_RM h3) = d.rh e (d.E0_le_RM he) := by
          show H.rho ⟨(n : X) * e * (n : X)⁻¹, d.RM_le (d.E0_le_RM h3)⟩ =
            H.rho ⟨e, d.RM_le (d.E0_le_RM he)⟩
          rw [show (⟨(n : X) * e * (n : X)⁻¹, d.RM_le (d.E0_le_RM h3)⟩ : ↥h.M3) =
            ⟨n, hNM n.2⟩ * ⟨e, d.RM_le (d.E0_le_RM he)⟩ * (⟨n, hNM n.2⟩ : ↥h.M3)⁻¹ from rfl,
            map_mul, map_mul, map_inv, hn1, one_mul, inv_one, mul_one]
        have h5 := d.rho_inj hCF1 hCF2 (d.E0_le_RM h3) (d.E0_le_RM he) h4
        calc e * (n : X) = ((n : X) * e * (n : X)⁻¹) * n := by rw [h5]
          _ = (n : X) * e := by group
      exact ⟨⟨n, hnC⟩, hn, rfl⟩
    · rintro _ ⟨n, hn, rfl⟩
      exact ⟨⟨n, d.CME0_le_NME0 n.2⟩, hn, rfl⟩
  have hk : Nat.card φN.ker = Nat.card φC.ker := by
    rw [← card_map_of_injective d.NME0.subtype_injective,
      ← card_map_of_injective d.CME0.subtype_injective, hkereq]
  rw [hrN] at h1
  rw [hrC, d.card_E0hat] at h2
  rw [← h1, ← h2, hk]
  ring

noncomputable abbrev OM (u : X) : Set X := Cat8.conjOrbit d.NME0 u

theorem OM_sub {u : X} (hu : u ∈ d.E0) : d.OM u ⊆ d.E0 := by
  rintro _ ⟨n, hn, rfl⟩
  exact d.conj_mem_E0 hn hu

open Classical in
noncomputable abbrev rhX (x : X) : MulAut (h.K ⧸ pPrimeCore 2 h.K) :=
  if hx : x ∈ d.RM then d.rh x hx else 1

theorem rhX_eq {x : X} (hx : x ∈ d.RM) : d.rhX x = d.rh x hx := by
  simp only [rhX, hx, ↓reduceDIte]

theorem image_OM (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) {u : X} (hu : u ∈ d.E0) :
    d.rhX '' d.OM u = Cat8.conjOrbit d.NE0hat (d.rh u (d.E0_le_RM hu)) := by
  ext w
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    have hc := d.conj_mem_E0 hn hu
    refine ⟨H.rho ⟨n, (Subgroup.mem_inf.mp hn).1⟩, d.rho_mem_NE0hat hn, ?_⟩
    rw [d.rhX_eq (d.E0_le_RM hc)]
    exact (d.conj_eq_iff hCF1 hCF2 hn hu hc).mp rfl
  · rintro ⟨w', hw', rfl⟩
    obtain ⟨n, hn, rfl⟩ := d.exists_lift_NE0hat hq hCF1 hCF2 hOut hw'
    have hc := d.conj_mem_E0 hn hu
    refine ⟨n⁻¹ * u * n, ⟨n, hn, rfl⟩, ?_⟩
    rw [d.rhX_eq (d.E0_le_RM hc)]
    exact ((d.conj_eq_iff hCF1 hCF2 hn hu hc).mp rfl).symm

theorem ncard_OM (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) {u : X} (hu : u ∈ d.E0) :
    (d.OM u).ncard = (Cat8.conjOrbit d.NE0hat (d.rh u (d.E0_le_RM hu))).ncard := by
  have hinj : Set.InjOn d.rhX (d.OM u) := by
    intro x hx y hy hxy
    have hx0 := d.E0_le_RM (d.OM_sub hu hx)
    have hy0 := d.E0_le_RM (d.OM_sub hu hy)
    rw [d.rhX_eq hx0, d.rhX_eq hy0] at hxy
    exact d.rho_inj hCF1 hCF2 hx0 hy0 hxy
  rw [← d.image_OM hq hCF1 hCF2 hOut hu, hinj.ncard_image]

theorem E0_le_closure (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {S : Set X}
    (hS : S ⊆ d.E0) (hT : d.E0hat ≤ closure (d.rhX '' S)) : d.E0 ≤ closure S := by
  have hcl : closure S ≤ d.E0 := (closure_le _).mpr hS
  have hle : closure (d.rhX '' S) ≤ ((closure S).subgroupOf h.M3).map H.rho := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxR := d.E0_le_RM (hS hx)
    rw [d.rhX_eq hxR]
    exact mem_map_of_mem H.rho
      (show (⟨x, d.RM_le hxR⟩ : ↥h.M3) ∈ (closure S).subgroupOf h.M3 from subset_closure hx)
  intro e he
  obtain ⟨m, hm, hme⟩ := mem_map.mp (hle (hT (d.rh_mem_E0hat he)))
  have hmR : (m : X) ∈ d.RM := d.E0_le_RM (hcl hm)
  have := d.rho_inj hCF1 hCF2 hmR (d.E0_le_RM he) hme
  rw [← this]
  exact hm

theorem rh_zt :
    d.rh (d.z * d.tau) (d.E0_le_RM (mul_mem d.z_mem_E0 d.tau_mem_E0)) = d.c.z * d.c.tau := by
  rw [d.rh_mul d.z_mem_RM d.tau_mem_RM, d.rh_z, d.rh_tau]

theorem ncard_OM_zt (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) :
    (d.OM (d.z * d.tau)).ncard = Nat.card (Cat8.conjOrbit d.NE0hat (d.c.z * d.c.tau)) := by
  rw [d.ncard_OM hq hCF1 hCF2 hOut (mul_mem d.z_mem_E0 d.tau_mem_E0), d.rh_zt,
    Nat.card_coe_set_eq]

theorem ncard_OM_z (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) : (d.OM d.z).ncard = Nat.card (Cat8.conjOrbit d.NE0hat d.c.z) := by
  rw [d.ncard_OM hq hCF1 hCF2 hOut d.z_mem_E0, d.rh_z, Nat.card_coe_set_eq]

theorem ne_one_of_mem_OM {u x : X} (hu : u ≠ 1) (hx : x ∈ d.OM u) : x ≠ 1 := by
  obtain ⟨n, -, rfl⟩ := hx
  intro h1
  apply hu
  calc u = n * (n⁻¹ * u * n) * n⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem zt_ne_one (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hL0 : CFQ3L0) : d.z * d.tau ≠ 1 := by
  intro h1
  apply d.tau_ne_z hq hCF1 hCF2 hL0
  calc d.tau = d.z * (d.z * d.tau) := by rw [← mul_assoc, d.z_sq, one_mul]
    _ = d.z := by rw [h1, mul_one]

theorem NME0_le_NE : d.NME0 ≤ d.NE := d.NME0_le_normalizer_E

noncomputable abbrev Ob : Set X := Cat8.conjOrbit d.NE d.b

theorem sub_Ob (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {v : X} (hvE : v ∈ d.NE)
    (hvb : v * d.b * v⁻¹ = d.tau * d.z * d.b) :
    insert d.b ((· * d.b) '' d.OM (d.z * d.tau)) ⊆ d.Ob := by
  rintro x (rfl | ⟨_, ⟨m, hm, rfl⟩, rfl⟩)
  · exact ⟨1, one_mem _, by group⟩
  · refine ⟨v⁻¹ * m, mul_mem (inv_mem hvE) (d.NME0_le_NE hm), ?_⟩
    have hmb := d.conj_b_NME0 hm
    calc (v⁻¹ * m)⁻¹ * d.b * (v⁻¹ * m) = m⁻¹ * (v * d.b * v⁻¹) * m := by group
      _ = m⁻¹ * (d.tau * d.z * d.b) * m := by rw [hvb]
      _ = m⁻¹ * (d.tau * d.z) * m * (m⁻¹ * d.b * m) := by group
      _ = m⁻¹ * (d.z * d.tau) * m * d.b := by
          rw [hmb, show d.tau * d.z = d.z * d.tau from d.tau_comm_z hCF1 hCF2]

theorem exists_v' (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    ∃ v ∈ d.NE, v * d.b * v⁻¹ = d.tau * d.z * d.b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hRU⟩ := (d.isPGroup_R hF.simple hF.inner).exists_le_sylow
  obtain ⟨P, -, hP2, hP512⟩ := d.exists_two_subgroup_centralizer_z hq hF
  have hU : 512 ≤ Nat.card (U : Subgroup X) := hP512 ▸ card_le_card_sylow hP2 U
  have hne : d.R ≠ U := by
    intro h1
    have h2 := d.card_R hF.simple hF.inner
    rw [h1] at h2
    omega
  obtain ⟨v, -, -, -, hvE, hvb⟩ := d.exists_v hq hF U.isPGroup' hRU hne
  exact ⟨v, hvE, hvb⟩

theorem conj_b_mem (hq : h.IsQ3) (hF : Cat8.Q3Facts) {e : X} (he : e ∈ d.E0) {g : X}
    (hg : g⁻¹ * d.b * g = e * d.b) : e = 1 ∨ e ∈ d.OM (d.z * d.tau) := by
  have hnf := d.not_fused hq hF
  rcases d.E0_cases hq hF.simple hF.inner hF.out he with h1 | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · exact Or.inl h1
  · exfalso
    apply (hnf (g * n⁻¹)).2.2.2.1
    have hnb := d.conj_b_NME0 hn
    calc (g * n⁻¹)⁻¹ * d.b * (g * n⁻¹) = n * (g⁻¹ * d.b * g) * n⁻¹ := by group
      _ = n * (n⁻¹ * d.z * n * d.b) * n⁻¹ := by rw [hg]
      _ = n * (n⁻¹ * d.z * n * (n⁻¹ * d.b * n)) * n⁻¹ := by rw [hnb]
      _ = d.z * d.b := by group
      _ = d.b * d.z := d.b_comm_z.symm
  · exact Or.inr ⟨n, hn, rfl⟩

theorem conj_bz_mem (hq : h.IsQ3) (hF : Cat8.Q3Facts) {e : X} (he : e ∈ d.E0) {g : X}
    (hg : g⁻¹ * (d.b * d.z) * g = e * d.b) : e ∈ d.OM d.z := by
  have hnf := d.not_fused hq hF
  rcases d.E0_cases hq hF.simple hF.inner hF.out he with rfl | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · exfalso
    apply (hnf g⁻¹).2.2.2.1
    rw [inv_inv]
    calc g * d.b * g⁻¹ = g * (g⁻¹ * (d.b * d.z) * g) * g⁻¹ := by rw [hg, one_mul]
      _ = d.b * d.z := by group
  · exact ⟨n, hn, rfl⟩
  · exfalso
    apply (hnf ((h.x * d.g * h.x * n) * g⁻¹)).2.2.2.1
    have hnb := d.conj_b_NME0 hn
    have hxgx := d.b_conj_xgx hq hF
    have htz := d.tau_comm_z hF.simple hF.inner
    calc ((h.x * d.g * h.x * n) * g⁻¹)⁻¹ * d.b * ((h.x * d.g * h.x * n) * g⁻¹)
        = g * (n⁻¹ * ((h.x * d.g * h.x)⁻¹ * d.b * (h.x * d.g * h.x)) * n) * g⁻¹ := by group
      _ = g * (n⁻¹ * (d.tau * d.z * d.b) * n) * g⁻¹ := by rw [hxgx]
      _ = g * (n⁻¹ * (d.z * d.tau) * n * (n⁻¹ * d.b * n)) * g⁻¹ := by
          rw [← htz]
          group
      _ = g * (n⁻¹ * (d.z * d.tau) * n * d.b) * g⁻¹ := by rw [hnb]
      _ = g * (g⁻¹ * (d.b * d.z) * g) * g⁻¹ := by rw [hg]
      _ = d.b * d.z := by group

theorem conj_mem_Eb (hq : h.IsQ3) (hF : Cat8.Q3Facts) {w : X} (hw : w ∈ d.E) (hw0 : w ∉ d.E0)
    {n : X} (hn : n ∈ d.NE) : ∃ e ∈ d.E0, n⁻¹ * w * n = e * d.b := by
  have hin : n⁻¹ * w * n ∈ d.E := by
    have := (mem_normalizer_iff.mp (inv_mem hn) w).mp hw
    rwa [inv_inv] at this
  obtain ⟨e, he, h1 | h1⟩ := d.mem_E_cases hin
  · exfalso
    have he' : n⁻¹ * w * n ∈ d.E0 := h1 ▸ he
    have hb' : n⁻¹⁻¹ * (n⁻¹ * w * n) * n⁻¹ = w := by group
    have h2 := d.E0_strongly_closed hq hF he' n⁻¹ (by rw [hb']; exact hw)
    rw [hb'] at h2
    exact hw0 h2
  · exact ⟨e, he, h1⟩

theorem b_not_mem_E0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : d.b ∉ d.E0 :=
  fun hb => d.b_not_mem_M3 hCF1 hCF2 (d.E0_le_M3 hb)

theorem mul_b_not_mem_E0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {e : X}
    (he : e ∈ d.E0) : e * d.b ∉ d.E0 := by
  intro h1
  apply d.b_not_mem_E0 hCF1 hCF2
  have := mul_mem (inv_mem he) h1
  rwa [inv_mul_cancel_left] at this

theorem Ob_sub (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    d.Ob ⊆ insert d.b ((· * d.b) '' d.OM (d.z * d.tau)) := by
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨e, he, h1⟩ := d.conj_mem_Eb hq hF d.b_mem_E (d.b_not_mem_E0 hF.simple hF.inner) hn
  rcases d.conj_b_mem hq hF he h1 with rfl | hO
  · exact Set.mem_insert_iff.mpr (Or.inl (by rw [h1, one_mul]))
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨e, hO, h1.symm⟩)

theorem ncard_Ob (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    d.Ob.ncard = 1 + (d.OM (d.z * d.tau)).ncard := by
  obtain ⟨v, hvE, hvb⟩ := d.exists_v' hq hF
  have heq : d.Ob = insert d.b ((· * d.b) '' d.OM (d.z * d.tau)) :=
    Set.Subset.antisymm (d.Ob_sub hq hF) (d.sub_Ob hF.simple hF.inner hvE hvb)
  have hnot : d.b ∉ (· * d.b) '' d.OM (d.z * d.tau) := by
    rintro ⟨u, hu, hub⟩
    have hub' : u * d.b = d.b := hub
    have hu1 : u = 1 := by
      calc u = u * d.b * d.b⁻¹ := by group
        _ = 1 := by rw [hub', mul_inv_cancel]
    exact d.ne_one_of_mem_OM (d.zt_ne_one hq hF.simple hF.inner hF.l0) hu hu1
  rw [heq, Set.ncard_insert_of_notMem hnot (Set.toFinite _),
    Set.ncard_image_of_injective _ (mul_left_injective d.b), add_comm]

noncomputable abbrev NEb : Subgroup X := d.NE ⊓ centralizer ({d.b} : Set X)

theorem card_NE_ge (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    720 * Nat.card d.CNE ≤ Nat.card d.NE := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  have hOut := hF.out
  have h1 := Eight.card_conjOrbit_mul d.NE d.b
  have hCNb : d.CNE ≤ d.NEb :=
    le_inf inf_le_left
      (inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr d.b_mem_E)))
  have hMNb : d.NME0 ≤ d.NEb := le_inf d.NME0_le_NE d.NME0_le_centralizer_b
  have h2 := Eight.card_mul_relIndex_of_le hCNb
  have h3 : d.CNE.relIndex d.NME0 ≤ d.CNE.relIndex d.NEb :=
    Subgroup.relIndex_le_of_le_right hMNb (by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite)
  have h4 : d.CNE.relIndex d.NME0 = d.CME0.relIndex d.NME0 := by
    rw [← Subgroup.inf_relIndex_right d.CNE d.NME0, d.CNE_inf_NME0]
  have h5 := Eight.card_mul_relIndex_of_le d.CME0_le_NME0
  have h6 := d.card_NME0_mul hq hCF1 hCF2 hOut
  have hpos : 0 < Nat.card d.CME0 := Nat.card_pos
  have h7 : d.CME0.relIndex d.NME0 * 16 = Nat.card d.NE0hat := by
    have h8 : Nat.card d.CME0 * (d.CME0.relIndex d.NME0 * 16) =
        Nat.card d.CME0 * Nat.card d.NE0hat := by
      rw [← mul_assoc, h5, h6, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h8
  have hOb := d.ncard_Ob hq hF
  have hr1 : d.CME0.relIndex d.NME0 ≤ d.CNE.relIndex d.NEb := by
    rw [← h4]
    exact h3
  rcases d.E0hat_card_cases with ⟨hN, -, hzt, -⟩ | ⟨hN, -, hzt, -⟩
  · have hr : d.CME0.relIndex d.NME0 = 120 := by omega
    have hO : d.Ob.ncard = 6 := by rw [hOb, d.ncard_OM_zt hq hCF1 hCF2 hOut, hzt]
    calc 720 * Nat.card d.CNE = 6 * (Nat.card d.CNE * 120) := by ring
      _ ≤ 6 * (Nat.card d.CNE * d.CNE.relIndex d.NEb) := by
          gcongr
          rw [← hr]
          exact hr1
      _ = d.Ob.ncard * Nat.card d.NEb := by rw [h2, hO]
      _ = Nat.card d.NE := h1
  · have hr : d.CME0.relIndex d.NME0 = 72 := by omega
    have hO : d.Ob.ncard = 10 := by rw [hOb, d.ncard_OM_zt hq hCF1 hCF2 hOut, hzt]
    calc 720 * Nat.card d.CNE = 10 * (Nat.card d.CNE * 72) := by ring
      _ ≤ 10 * (Nat.card d.CNE * d.CNE.relIndex d.NEb) := by
          gcongr
          rw [← hr]
          exact hr1
      _ = d.Ob.ncard * Nat.card d.NEb := by rw [h2, hO]
      _ = Nat.card d.NE := h1

theorem conj_mem_conjOrbit {w n x : X} (hn : n ∈ d.NE) (hx : x ∈ Cat8.conjOrbit d.NE w) :
    n * x * n⁻¹ ∈ Cat8.conjOrbit d.NE w := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨m * n⁻¹, mul_mem hm (inv_mem hn), by group⟩

theorem exists_class (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    ∃ C : Set X, C ⊆ d.E ∧ (∀ x ∈ C, x ∉ d.E0) ∧ C.ncard = 6 ∧
      (∀ n ∈ d.NE, ∀ x ∈ C, n * x * n⁻¹ ∈ C) ∧ closure C = d.E := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  have hOut := hF.out
  have hbE := d.b_mem_E
  have hb0 := d.b_not_mem_E0 hCF1 hCF2
  have hzE0 := d.z_mem_E0
  have hbzE : d.b * d.z ∈ d.E := mul_mem hbE (d.E0_le_E hzE0)
  have hbz0 : d.b * d.z ∉ d.E0 := by
    rw [d.b_comm_z]
    exact d.mul_b_not_mem_E0 hCF1 hCF2 hzE0
  have hcls : ∀ w ∈ d.E, w ∉ d.E0 → ∀ x ∈ Cat8.conjOrbit d.NE w, x ∈ d.E ∧ x ∉ d.E0 := by
    rintro w hw hw0 _ ⟨n, hn, rfl⟩
    obtain ⟨e, he, h1⟩ := d.conj_mem_Eb hq hF hw hw0 hn
    rw [h1]
    exact ⟨mul_mem (d.E0_le_E he) hbE, d.mul_b_not_mem_E0 hCF1 hCF2 he⟩
  rcases d.E0hat_card_cases with ⟨-, -, hzt, hgen⟩ | ⟨-, hz, -, hgen⟩
  ·
    refine ⟨d.Ob, fun x hx => (hcls _ hbE hb0 x hx).1, fun x hx => (hcls _ hbE hb0 x hx).2, ?_,
      fun n hn x hx => d.conj_mem_conjOrbit hn hx, ?_⟩
    · rw [d.ncard_Ob hq hF, d.ncard_OM_zt hq hCF1 hCF2 hOut, hzt]
    · apply le_antisymm
      · exact (closure_le _).mpr fun x hx => (hcls _ hbE hb0 x hx).1
      · obtain ⟨v, hvE, hvb⟩ := d.exists_v' hq hF
        have hsub := d.sub_Ob hCF1 hCF2 hvE hvb
        have hbC : d.b ∈ closure d.Ob := subset_closure (hsub (Set.mem_insert _ _))
        have hzt0 : d.z * d.tau ∈ d.E0 := mul_mem hzE0 d.tau_mem_E0
        have hE0 : d.E0 ≤ closure d.Ob := by
          refine (d.E0_le_closure hCF1 hCF2 (d.OM_sub hzt0) ?_).trans ?_
          · have h1 := hgen
            rw [← d.rh_zt, ← d.image_OM hq hCF1 hCF2 hOut hzt0] at h1
            exact h1.ge
          · rw [closure_le]
            intro u hu
            have h1 : u * d.b ∈ closure d.Ob := subset_closure (hsub (Set.mem_insert_of_mem _
              ⟨u, hu, rfl⟩))
            have := mul_mem h1 (inv_mem hbC)
            rwa [mul_inv_cancel_right] at this
        refine sup_le hE0 ?_
        rw [d.B_eq, zpowers_le]
        exact hbC
  ·
    have hOz : Cat8.conjOrbit d.NE (d.b * d.z) = (· * d.b) '' d.OM d.z := by
      apply Set.Subset.antisymm
      · rintro _ ⟨n, hn, rfl⟩
        obtain ⟨e, he, h1⟩ := d.conj_mem_Eb hq hF hbzE hbz0 hn
        exact ⟨e, d.conj_bz_mem hq hF he h1, h1.symm⟩
      · rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
        refine ⟨m, d.NME0_le_NE hm, ?_⟩
        calc m⁻¹ * (d.b * d.z) * m = m⁻¹ * d.z * m * (m⁻¹ * d.b * m) := by
              rw [d.b_comm_z]
              group
          _ = m⁻¹ * d.z * m * d.b := by rw [d.conj_b_NME0 hm]
    refine ⟨Cat8.conjOrbit d.NE (d.b * d.z), fun x hx => (hcls _ hbzE hbz0 x hx).1,
      fun x hx => (hcls _ hbzE hbz0 x hx).2, ?_, fun n hn x hx => d.conj_mem_conjOrbit hn hx, ?_⟩
    · rw [hOz, Set.ncard_image_of_injective _ (mul_left_injective d.b),
        d.ncard_OM_z hq hCF1 hCF2 hOut, hz]
    · apply le_antisymm
      · exact (closure_le _).mpr fun x hx => (hcls _ hbzE hbz0 x hx).1
      · have hmem : ∀ u ∈ d.OM d.z, u * d.b ∈ closure (Cat8.conjOrbit d.NE (d.b * d.z)) :=
          fun u hu => subset_closure (by rw [hOz]; exact ⟨u, hu, rfl⟩)
        have hS : {y | ∃ u ∈ d.OM d.z, ∃ w ∈ d.OM d.z, y = u * w} ⊆ d.E0 := by
          rintro _ ⟨u, hu, w, hw, rfl⟩
          exact mul_mem (d.OM_sub hzE0 hu) (d.OM_sub hzE0 hw)
        have hE0 : d.E0 ≤ closure (Cat8.conjOrbit d.NE (d.b * d.z)) := by
          refine (d.E0_le_closure hCF1 hCF2 hS ?_).trans ?_
          · rw [← hgen]
            apply Subgroup.closure_mono
            rintro _ ⟨u', hu', w', hw', rfl⟩
            rw [← d.rh_z d.z_mem_RM, ← d.image_OM hq hCF1 hCF2 hOut hzE0] at hu' hw'
            obtain ⟨u, hu, rfl⟩ := hu'
            obtain ⟨w, hw, rfl⟩ := hw'
            have hu0 := d.E0_le_RM (d.OM_sub hzE0 hu)
            have hw0 := d.E0_le_RM (d.OM_sub hzE0 hw)
            refine ⟨u * w, ⟨u, hu, w, hw, rfl⟩, ?_⟩
            rw [d.rhX_eq (mul_mem hu0 hw0), d.rhX_eq hu0, d.rhX_eq hw0, d.rh_mul hu0 hw0]
          · rw [closure_le]
            rintro _ ⟨u, hu, w, hw, rfl⟩
            have h1 := mul_mem (hmem u hu) (hmem w hw)
            have hwb := d.b_comm_E0 (d.OM_sub hzE0 hw)
            rwa [show u * d.b * (w * d.b) = u * w by
              rw [mul_assoc u d.b, ← mul_assoc d.b w d.b, ← hwb, mul_assoc w d.b d.b,
                d.b_mul_self, mul_one]] at h1
        have hbC : d.b ∈ closure (Cat8.conjOrbit d.NE (d.b * d.z)) := by
          have h1 := hmem d.z ⟨1, one_mem _, by group⟩
          have := mul_mem (inv_mem (hE0 hzE0)) h1
          rwa [inv_mul_cancel_left] at this
        refine sup_le hE0 ?_
        rw [d.B_eq, zpowers_le]
        exact hbC

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
