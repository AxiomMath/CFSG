module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFusionDef

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private lemma s3_zpowers_eq_one_or_self {H : Type} [Group H] {z : H} (hz : orderOf z = 2)
    {y : H} (hy : y ∈ zpowers z) : y = 1 ∨ y = z := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hmod := zpow_mod_orderOf z k
  rw [hz] at hmod
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← hk, ← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
    simp
  · right
    rw [← hk, ← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
    simp

private lemma s3_Z_le_zt (s : Setting3 G L) : s.fr.Z ≤ zt s :=
  Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))

private lemma s3_t_mem_zt (s : Setting3 G L) : s.t ∈ zt s :=
  Subgroup.subset_closure (by simp)

private lemma s3_t_mem_cen_R (s : Setting3 G L) : s.t ∈ cen s.R := by
  refine Subgroup.mem_inf.mpr ⟨s3_t_mem_R s, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact s3_comm_t_of_mem_T s (s.R_le_T hu)

theorem s3_R_cases (hS : HRSetting G L) (h31 : s.Fact31) :
    ∀ r ∈ s.R, ∃ y ∈ s.fr.S, r = y ∨ r = y * s.t := by
  intro r hr
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  have hrT : r ∈ s.T := s.R_le_T hr
  have hrN : r ∈ normalizer (L : Set G) := s3_T_le_N s hS hrT
  let α : MulAut (L ⧸ center L) := jHom L ⟨r, hrN⟩
  have hαacts : ActsAs L r α := jHom_actsAs L ⟨r, hrN⟩
  have hαR : α ∈ jSub L s.R := (mem_jSub L).mpr ⟨r, hr, hαacts⟩
  rw [s3_jSub_R s] at hαR
  rw [← s3_jSub_S s] at hαR
  obtain ⟨y, hyS, hyα⟩ := (mem_jSub L).mp hαR
  have hyT : y ∈ s.T := s3_S_le_T s hyS
  have hc : y⁻¹ * r ∈ s.T ⊓ centralizer (L : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨s.T.mul_mem (s.T.inv_mem hyT) hrT, ?_⟩
    apply (actsAs_one_iff L).mp
    have h1 : ActsAs L (y⁻¹ * r) (α⁻¹ * α) := actsAs_mul L (actsAs_inv L hyα) hαacts
    simpa using h1
  rw [s3_T_inf_centralizer s h31] at hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hkmod := zpow_mod_orderOf s.t k
  rw [s.t_order] at hkmod
  refine ⟨y, hyS, ?_⟩
  have hrk : r = y * s.t ^ k := by rw [hk]; group
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    have hk1 : s.t ^ k = 1 := by
      rw [← hkmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
      simp
    rw [hrk, hk1, mul_one]
  · right
    have hk1 : s.t ^ k = s.t := by
      rw [← hkmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
      simp
    rw [hrk, hk1]

private lemma s3_z_mem_cen_R (hS : HRSetting G L) (hA : LFactsA s) (h31 : s.Fact31) :
    s.fr.z ∈ cen s.R := by
  have hzS : s.fr.z ∈ s.fr.S := s3_A_le_S s (s3_z_mem_A s)
  have hzcen : s.fr.z ∈ cen s.fr.S := (hA.cen_S).symm ▸ Subgroup.mem_zpowers s.fr.z
  have hzcenS : s.fr.z ∈ Subgroup.centralizer (s.fr.S : Set G) :=
    (Subgroup.mem_inf.mp hzcen).2
  refine Subgroup.mem_inf.mpr ⟨s.S_le_R hzS, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  rcases s3_R_cases s hS h31 u hu with ⟨y, hyS, hy | hy⟩
  · rw [hy]
    exact Subgroup.mem_centralizer_iff.mp hzcenS y hyS
  · rw [hy]
    have hzy : y * s.fr.z = s.fr.z * y := Subgroup.mem_centralizer_iff.mp hzcenS y hyS
    have hzt : s.fr.z * s.t = s.t * s.fr.z := s3_comm_t_of_mem_L s (s3_z_mem_L s)
    calc (y * s.t) * s.fr.z = y * (s.t * s.fr.z) := by group
      _ = y * (s.fr.z * s.t) := by rw [← hzt]
      _ = (y * s.fr.z) * s.t := by group
      _ = (s.fr.z * y) * s.t := by rw [hzy]
      _ = s.fr.z * (y * s.t) := by group

private lemma s3_cen_R_le_zt (hS : HRSetting G L) (hA : LFactsA s) (h31 : s.Fact31) :
    cen s.R ≤ zt s := by
  intro r hr
  obtain ⟨hrR, -⟩ := Subgroup.mem_inf.mp hr
  have htC := s3_t_mem_cen_R s
  rcases s3_R_cases s hS h31 r hrR with ⟨y, hyS, hy | hy⟩
  · have hyC : y ∈ cen s.R := hy ▸ hr
    have hyZ : y ∈ s.fr.Z := by
      rw [← hA.cen_S]
      exact Subgroup.mem_inf.mpr ⟨hyS, fun u hu =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyC).2) u (s.S_le_R hu)⟩
    rw [hy]
    exact s3_Z_le_zt s hyZ
  · have hyC : y ∈ cen s.R := by
      have h : y = r * s.t⁻¹ := by rw [hy]; group
      rw [h]
      exact (cen s.R).mul_mem hr ((cen s.R).inv_mem htC)
    have hyZ : y ∈ s.fr.Z := by
      rw [← hA.cen_S]
      exact Subgroup.mem_inf.mpr ⟨hyS, fun u hu =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyC).2) u (s.S_le_R hu)⟩
    rw [hy]
    exact mul_mem (s3_Z_le_zt s hyZ) (s3_t_mem_zt s)

theorem s3_T_comm_z (hS : HRSetting G L) (hA : LFactsA s) {g : G} (hg : g ∈ s.T) :
    g * s.fr.z * g⁻¹ = s.fr.z := by
  have hSleT : s.fr.S ≤ s.T := s3_S_le_T s
  have hnormS : (s.fr.S.subgroupOf s.T).Normal := s3_S_normal_T s hS
  have hzS : s.fr.z ∈ s.fr.S := s3_A_le_S s (s3_z_mem_A s)
  have hzT : s.fr.z ∈ s.T := hSleT hzS
  have hconjS : g * s.fr.z * g⁻¹ ∈ s.fr.S := by
    have h := hnormS.conj_mem ⟨s.fr.z, hzT⟩ (Subgroup.mem_subgroupOf.mpr hzS) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.mp h
  have hconj_invS : ∀ u ∈ s.fr.S, g⁻¹ * u * g ∈ s.fr.S := by
    intro u hu
    have h := hnormS.conj_mem ⟨u, hSleT hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
      ⟨g⁻¹, s.T.inv_mem hg⟩
    simpa using Subgroup.mem_subgroupOf.mp h
  have hzcen : s.fr.z ∈ cen s.fr.S := (hA.cen_S).symm ▸ Subgroup.mem_zpowers s.fr.z
  have hzcent : s.fr.z ∈ Subgroup.centralizer (s.fr.S : Set G) :=
    (Subgroup.mem_inf.mp hzcen).2
  have hconj_cen : g * s.fr.z * g⁻¹ ∈ Subgroup.centralizer (s.fr.S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hzu : (g⁻¹ * u * g) * s.fr.z = s.fr.z * (g⁻¹ * u * g) :=
      Subgroup.mem_centralizer_iff.mp hzcent (g⁻¹ * u * g) (hconj_invS u hu)
    calc u * (g * s.fr.z * g⁻¹)
        = g * ((g⁻¹ * u * g) * s.fr.z) * g⁻¹ := by group
      _ = g * (s.fr.z * (g⁻¹ * u * g)) * g⁻¹ := by rw [hzu]
      _ = (g * s.fr.z * g⁻¹) * u := by group
  have hyZ : g * s.fr.z * g⁻¹ ∈ s.fr.Z := by
    have hmem : g * s.fr.z * g⁻¹ ∈ cen s.fr.S := Subgroup.mem_inf.mpr ⟨hconjS, hconj_cen⟩
    rwa [hA.cen_S] at hmem
  rw [SFrame.Z] at hyZ
  have hz1 : s.fr.z ≠ 1 := by
    intro h
    have hord := hA.z_order
    rw [h, orderOf_one] at hord
    norm_num at hord
  rcases s3_zpowers_eq_one_or_self hA.z_order hyZ with h1 | hz
  · exfalso
    exact hz1 (by
      have h := congrArg (fun w => g⁻¹ * w * g) h1
      simpa [mul_assoc] using h)
  · exact hz

theorem s3_T_normal_T1 (hA : LFactsA s) (h31 : s.Fact31) (e : Setting3.Ext s) :
    (s.T.subgroupOf e.T₁).Normal := by
  apply Subgroup.normal_of_index_eq_two
  simpa only [Subgroup.relIndex] using (fusionDef_orbit s hA h31 e).1

theorem s3_T1_conj_t (hA : LFactsA s) (h31 : s.Fact31) (e : Setting3.Ext s) {x : G}
    (hx : x ∈ e.T₁) (hxT : x ∉ s.T) : x * s.t * x⁻¹ = s.fr.z * s.t := by
  have hconj : x * s.t * x⁻¹ ∈ conjClass e.T₁ s.t := ⟨x, hx, rfl⟩
  rw [(fusionDef_orbit s hA h31 e).2] at hconj
  obtain ⟨y, hy, hyeq⟩ := hconj
  rw [hA.cen_S, SFrame.Z] at hy
  rcases s3_zpowers_eq_one_or_self hA.z_order hy with hy1 | hyz
  · exfalso
    apply hxT
    rw [← s3_inf_H_T1 s e]
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [hy1] using hyeq)
  · rw [hyz] at hyeq
    exact hyeq

theorem s3_T1_comm_z (hS : HRSetting G L) (hA : LFactsA s) (h31 : s.Fact31)
    (e : Setting3.Ext s) {x : G} (hx : x ∈ e.T₁) : x * s.fr.z * x⁻¹ = s.fr.z := by
  by_cases hxT : x ∈ s.T
  · exact s3_T_comm_z s hS hA hxT
  · have hzC : s.fr.z ∈ cen s.R := s3_z_mem_cen_R s hS hA h31
    have hz'C : x * s.fr.z * x⁻¹ ∈ cen s.R :=
      (Subgroup.mem_normalizer_iff.mp (e.sylow.1 hx) s.fr.z).mp hzC
    have hz'zt : x * s.fr.z * x⁻¹ ∈ zt s := s3_cen_R_le_zt s hS hA h31 hz'C
    have hz1 : s.fr.z ≠ 1 := by
      intro h
      have hord := hA.z_order
      rw [h, orderOf_one] at hord
      norm_num at hord
    have hzt4 := s3_T1_conj_t s hA h31 e hx hxT
    rcases (s3_mem_zt_iff s hA).mp hz'zt with h1 | hz | ht | hzt
    · exact absurd (by
        have h := congrArg (fun w => x⁻¹ * w * x) h1
        simpa [mul_assoc] using h) hz1
    · exact hz
    · exfalso
      have hz : s.fr.z = x⁻¹ * s.t * x := by
        have h := congrArg (fun w => x⁻¹ * w * x) ht
        simpa [mul_assoc] using h
      apply h31.2.2.1 x⁻¹
      rw [inv_inv, ← hz]
      exact s3_z_mem_L s
    · exfalso
      have hconj : x * s.fr.z * x⁻¹ = x * s.t * x⁻¹ := by rw [hzt, hzt4]
      have hzt_eq : s.fr.z = s.t := by
        have h := congrArg (fun w => x⁻¹ * w * x) hconj
        simpa [mul_assoc] using h
      exact s3_t_ne_z s h31 hzt_eq.symm

private lemma mem_sup_of_comm {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {w : G} (hw : w ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = w := by
  rw [Subgroup.sup_eq_closure] at hw
  refine Subgroup.closure_induction (p := fun w _ => ∃ h ∈ H, ∃ k ∈ K, h * k = w)
    ?_ ?_ ?_ ?_ hw
  · intro x hx
    rcases hx with hxH | hxK
    · exact ⟨x, hxH, 1, K.one_mem, by simp⟩
    · exact ⟨1, H.one_mem, x, hxK, by simp⟩
  · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
  · intro _ _ _ _ hx hy
    obtain ⟨h₁, hh₁, k₁, hk₁, hk1⟩ := hx
    obtain ⟨h₂, hh₂, k₂, hk₂, hk2⟩ := hy
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    rw [← hk1, ← hk2]
    calc (h₁ * h₂) * (k₁ * k₂) = h₁ * (h₂ * k₁) * k₂ := by group
      _ = h₁ * (k₁ * h₂) * k₂ := by rw [hcomm h₂ hh₂ k₁ hk₁]
      _ = (h₁ * k₁) * (h₂ * k₂) := by group
  · intro _ _ hx
    obtain ⟨h, hh, k, hk, hk1⟩ := hx
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    rw [← hk1, mul_inv_rev, ← hcomm h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)]

theorem s3_mem_A_sup_t {w : G} (hw : w ∈ s.fr.A ⊔ zpowers s.t) :
    ∃ a ∈ s.fr.A, w = a ∨ w = a * s.t := by
  have htA : s.t ∈ Subgroup.centralizer (s.fr.A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr (fun a ha => s3_comm_t_of_mem_A s ha)
  have hcomm : ∀ h ∈ s.fr.A, ∀ k ∈ zpowers s.t, h * k = k * h := by
    intro h hh k hk
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le.mpr htA hk) h hh
  obtain ⟨a, ha, k, hk, hak⟩ := mem_sup_of_comm (H := s.fr.A) (K := zpowers s.t) hcomm hw
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hkmod := zpow_mod_orderOf s.t j
  rw [s.t_order] at hkmod
  refine ⟨a, ha, ?_⟩
  have hw' : w = a * s.t ^ j := hak.symm
  rcases Int.emod_two_eq_zero_or_one j with h0 | h1
  · left
    have hk1 : s.t ^ j = 1 := by
      rw [← hkmod, show j % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
      simp
    rw [hw', hk1, mul_one]
  · right
    have hk1 : s.t ^ j = s.t := by
      rw [← hkmod, show j % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
      simp
    rw [hw', hk1]

end CFSG.OddStandard.HigherRank.YamadaG23
