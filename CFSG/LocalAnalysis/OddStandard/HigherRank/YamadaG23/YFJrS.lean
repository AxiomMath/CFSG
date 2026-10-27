module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFJr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFR

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private theorem s3_jOn_mem_Z_iff (hS : HRSetting G L) (h31 : s.Fact31) (hA : LFactsA s)
    {x : ↥s.T} :
    jOn L (s3_T_le_N s hS) x ∈ s.fr'.Z ↔ (x : G) ∈ zt s := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  have hzT : s.fr.z ∈ s.T := s3_z_mem_T s
  have htT : s.t ∈ s.T := s3_t_mem_T s
  have hzJ : jOn L (s3_T_le_N s hS) ⟨s.fr.z, hzT⟩ = s.fr'.z :=
    actsAs_unique L (jOn_actsAs L (s3_T_le_N s hS) ⟨s.fr.z, hzT⟩)
      (s3_actsAs_gens s).2.2.2.2.2
  have htJ : jOn L (s3_T_le_N s hS) ⟨s.t, htT⟩ = 1 :=
    actsAs_unique L (jOn_actsAs L (s3_T_le_N s hS) ⟨s.t, htT⟩)
      (actsAs_of_mem_centralizer L s.t_mem)
  constructor
  · intro hxZ
    have hx' : jOn L (s3_T_le_N s hS) x ∈ jSub L s.fr.Z := by
      rwa [s3_jSub_Z s]
    obtain ⟨w, hwZ, hwActs⟩ := (mem_jSub L).mp hx'
    rw [SFrame.Z] at hwZ
    have hwA : w ∈ s.fr.A := Subgroup.zpowers_le.mpr (s3_z_mem_A s) hwZ
    have hwT : w ∈ s.T := s3_A_le_T s hwA
    have hcen : w⁻¹ * (x : G) ∈ centralizer (L : Set G) := by
      refine (actsAs_one_iff L).mp ?_
      have h1 : ActsAs L w⁻¹ (jOn L (s3_T_le_N s hS) x)⁻¹ := actsAs_inv L hwActs
      have h2 : ActsAs L x (jOn L (s3_T_le_N s hS) x) :=
        jOn_actsAs L (s3_T_le_N s hS) x
      simpa using actsAs_mul L h1 h2
    have hmem : w⁻¹ * (x : G) ∈ s.T ⊓ centralizer (L : Set G) :=
      Subgroup.mem_inf.mpr ⟨s.T.mul_mem (s.T.inv_mem hwT) x.2, hcen⟩
    rw [s3_T_inf_centralizer s h31] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hxeq : (x : G) = w * s.t ^ k := by rw [hk]; group
    rw [hxeq]
    exact Subgroup.mul_mem _
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hwZ)
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
        (Subgroup.zpow_mem_zpowers s.t k))
  · intro hxzt
    rw [s3_mem_zt_iff s hA] at hxzt
    rcases hxzt with h1 | hz | ht | hzt
    · rw [show x = 1 from Subtype.ext h1, map_one]
      exact Subgroup.one_mem _
    · rw [show x = ⟨s.fr.z, hzT⟩ from Subtype.ext hz, hzJ]
      exact Subgroup.mem_zpowers s.fr'.z
    · rw [show x = ⟨s.t, htT⟩ from Subtype.ext ht, htJ]
      exact Subgroup.one_mem _
    · rw [show x = ⟨s.fr.z, hzT⟩ * ⟨s.t, htT⟩ from Subtype.ext hzt]
      rw [map_mul, hzJ, htJ, mul_one]
      exact Subgroup.mem_zpowers s.fr'.z

private theorem s3_jOn_mem_A_iff (hS : HRSetting G L) (h31 : s.Fact31) (hA : LFactsA s)
    {x : ↥s.T} :
    jOn L (s3_T_le_N s hS) x ∈ s.fr'.A ↔ (x : G) ∈ s.fr.A ⊔ zpowers s.t := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  have htT : s.t ∈ s.T := s3_t_mem_T s
  have htJ : jOn L (s3_T_le_N s hS) ⟨s.t, htT⟩ = 1 :=
    actsAs_unique L (jOn_actsAs L (s3_T_le_N s hS) ⟨s.t, htT⟩)
      (actsAs_of_mem_centralizer L s.t_mem)
  constructor
  · intro hxA'
    have hxA'' : jOn L (s3_T_le_N s hS) x ∈ jSub L s.fr.A := by rwa [s3_jSub_A s]
    obtain ⟨a, haA, haActs⟩ := (mem_jSub L).mp hxA''
    have hcen : a⁻¹ * (x : G) ∈ centralizer (L : Set G) := by
      refine (actsAs_one_iff L).mp ?_
      have h1 : ActsAs L a⁻¹ (jOn L (s3_T_le_N s hS) x)⁻¹ := actsAs_inv L haActs
      have h2 : ActsAs L x (jOn L (s3_T_le_N s hS) x) :=
        jOn_actsAs L (s3_T_le_N s hS) x
      simpa using actsAs_mul L h1 h2
    have hmem : a⁻¹ * (x : G) ∈ s.T ⊓ centralizer (L : Set G) :=
      Subgroup.mem_inf.mpr ⟨s.T.mul_mem (s.T.inv_mem (s3_A_le_T s haA)) x.2, hcen⟩
    rw [s3_T_inf_centralizer s h31] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hxeq : (x : G) = a * s.t ^ k := by rw [hk]; group
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haA)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers s.t k))
  · intro hxA
    obtain ⟨a, haA, hax | hax⟩ := s3_mem_A_sup_t s hxA
    · have haJ : jOn L (s3_T_le_N s hS) ⟨a, s3_A_le_T s haA⟩ ∈ s.fr'.A := by
        have h := (mem_jSub L).mpr ⟨a, haA,
          jOn_actsAs L (s3_T_le_N s hS) ⟨a, s3_A_le_T s haA⟩⟩
        rwa [s3_jSub_A s] at h
      rwa [show x = ⟨a, s3_A_le_T s haA⟩ from Subtype.ext hax]
    · have haJ : jOn L (s3_T_le_N s hS) ⟨a, s3_A_le_T s haA⟩ ∈ s.fr'.A := by
        have h := (mem_jSub L).mpr ⟨a, haA,
          jOn_actsAs L (s3_T_le_N s hS) ⟨a, s3_A_le_T s haA⟩⟩
        rwa [s3_jSub_A s] at h
      rw [show x = ⟨a, s3_A_le_T s haA⟩ * ⟨s.t, htT⟩ from Subtype.ext hax]
      rw [map_mul, htJ, mul_one]
      exact haJ

theorem s3_jr_section (hS : HRSetting G L) (hOut : (innerAut (L ⧸ center L)).index = 2)
    (h31 : s.Fact31) (hA : LFactsA s) (hRT : s.R ≠ s.T) :
    SecProp s.T (zt s) (fun Y _ _ π =>
      thompsonRank (⊤ : Subgroup Y) = ((s.fr.A ⊔ zpowers s.t).subgroupOf s.T).map π) := by
  have hrange : (jOn L (s3_T_le_N s hS)).range = s.fr'.Sσ := by
    rw [range_jOn L (s3_T_le_N s hS), s3_jSub_T s hS hOut hRT]
  let φ : ↥s.T →* ↥s.fr'.Sσ := (jOn L (s3_T_le_N s hS)).codRestrict s.fr'.Sσ
    (fun x => by rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hφ : Function.Surjective φ := by
    intro y
    have hy : (y : MulAut (L ⧸ center L)) ∈ (jOn L (s3_T_le_N s hS)).range := by
      rw [hrange]; exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨hN', hJ'⟩ := s.facts.2.2.2.2.1.2.2.1
  have hNA : (s.fr'.Z.subgroupOf s.fr'.Sσ) ≤ (s.fr'.A.subgroupOf s.fr'.Sσ) :=
    Subgroup.subgroupOf_mono s.fr'.Sσ (by
      rw [← s3_jSub_Z s, ← s3_jSub_A s]
      exact jSub_mono L (Subgroup.zpowers_le.mpr (s3_z_mem_A s)))
  have hM_eq : (zt s).subgroupOf s.T = (s.fr'.Z.subgroupOf s.fr'.Sσ).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact (s3_jOn_mem_Z_iff s hS h31 hA).symm
  have hA_eq : (s.fr'.A.subgroupOf s.fr'.Sσ).comap φ =
      (s.fr.A ⊔ zpowers s.t).subgroupOf s.T := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact s3_jOn_mem_A_iff s hS h31 hA
  have hZ : ((zt s).subgroupOf s.T).Normal := hM_eq.symm ▸ hN'.comap φ
  haveI := hN'
  haveI := hZ
  refine ⟨hZ, ?_⟩
  have hpull := thompsonRank_top_pullback φ hφ hNA (M := (zt s).subgroupOf s.T) hM_eq hJ'
  rw [hA_eq] at hpull
  exact hpull

end CFSG.OddStandard.HigherRank.YamadaG23
