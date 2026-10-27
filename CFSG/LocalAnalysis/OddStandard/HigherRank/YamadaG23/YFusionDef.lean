module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

@[instance_reducible] private def yfd_conjAct (N : Subgroup G) : MulAction ↥N G where
  smul x y := (x : G) * y * (x : G)⁻¹
  one_smul y := by
    show ((1 : ↥N) : G) * y * ((1 : ↥N) : G)⁻¹ = y
    simp
  mul_smul x y z := by
    show ((x * y : ↥N) : G) * z * ((x * y : ↥N) : G)⁻¹ =
      (x : G) * ((y : G) * z * (y : G)⁻¹) * (x : G)⁻¹
    simp [mul_assoc]

private lemma yfd_tCoset_cen_S (hA : LFactsA s) :
    s.tCoset (cen s.fr.S) = {s.t, s.fr.z * s.t} := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hA.cen_S] at hy
    rw [SFrame.Z] at hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hmod := zpow_mod_orderOf s.fr.z k
    rw [hA.z_order] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      have hk : s.fr.z ^ k = 1 := by
        rw [← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
        simp
      rw [hk, one_mul]
    · right
      have hk : s.fr.z ^ k = s.fr.z := by
        rw [← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
        simp
      rw [hk]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by simp⟩
    · exact ⟨s.fr.z, by rw [hA.cen_S, SFrame.Z]; exact Subgroup.mem_zpowers s.fr.z, rfl⟩

private lemma yfd_z_mul_t_ne_t (hA : LFactsA s) : s.fr.z * s.t ≠ s.t := by
  intro h
  have hz1 : s.fr.z = 1 := by
    apply mul_right_cancel (b := s.t)
    simpa using h
  have hord := hA.z_order
  rw [hz1, orderOf_one] at hord
  norm_num at hord

private lemma yfd_relIndex_inf_H_eq_two (N : Subgroup G) (hA : LFactsA s)
    (hconj : conjClass N s.t = s.tCoset (cen s.fr.S)) :
    (N ⊓ s.H).relIndex N = 2 := by
  letI := yfd_conjAct (G := G) N
  have hidx := MulAction.index_stabilizer ↥N s.t
  have hstab : MulAction.stabilizer ↥N s.t = (N ⊓ s.H).subgroupOf N := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change (x : G) * s.t * (x : G)⁻¹ = s.t ↔ (x : G) ∈ N ⊓ s.H
    rw [Subgroup.mem_inf, Setting3.H, Subgroup.mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have horb : (MulAction.orbit ↥N s.t).ncard = 2 := by
    have h1 : MulAction.orbit ↥N s.t = conjClass N s.t := by
      ext w
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨(x : G), x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [h1, hconj, yfd_tCoset_cen_S s hA]
    exact Set.ncard_pair (yfd_z_mul_t_ne_t s hA).symm
  rw [hstab, horb] at hidx
  unfold Subgroup.relIndex
  exact hidx

private lemma yfd_conjClass_T1 (hA : LFactsA s) (h31 : s.Fact31) (e : Setting3.Ext s) :
    conjClass e.T₁ s.t = s.tCoset (cen s.fr.S) := by
  have hN : conjClass (normalizer (cen s.R : Set G)) s.t = s.tCoset (cen s.fr.S) := h31.2.2.2
  have hsub : conjClass e.T₁ s.t ⊆ conjClass (normalizer (cen s.R : Set G)) s.t := by
    rintro w ⟨x, hx, rfl⟩
    exact ⟨x, e.sylow.1 hx, rfl⟩
  have hpair : ({s.t, s.fr.z * s.t} : Set G) ⊆ conjClass e.T₁ s.t := by
    have hnotle : ¬ e.T₁ ≤ s.H := by
      intro hle
      have hle' : e.T₁ ≤ normalizer (cen s.R : Set G) ⊓ s.H := le_inf e.sylow.1 hle
      have hrel := Subgroup.relIndex_mul_relIndex (H := e.T₁)
        (K := normalizer (cen s.R : Set G) ⊓ s.H) (L := normalizer (cen s.R : Set G))
        hle' inf_le_left
      have hdvd : 2 ∣ e.T₁.relIndex (normalizer (cen s.R : Set G)) := by
        rw [← hrel, yfd_relIndex_inf_H_eq_two s (normalizer (cen s.R : Set G)) hA hN]
        exact dvd_mul_left 2 _
      exact e.sylow.2.2 hdvd
    obtain ⟨x, hxT₁, hxH⟩ := SetLike.not_le_iff_exists.mp hnotle
    have hxconj : x * s.t * x⁻¹ ≠ s.t := by
      intro h
      apply hxH
      rw [Setting3.H, Subgroup.mem_centralizer_singleton_iff]
      have := congrArg (· * x) h
      simpa [mul_assoc] using this
    have hxmem : x * s.t * x⁻¹ ∈ conjClass e.T₁ s.t := ⟨x, hxT₁, rfl⟩
    have hxN : x * s.t * x⁻¹ ∈ conjClass (normalizer (cen s.R : Set G)) s.t := hsub hxmem
    rw [hN, yfd_tCoset_cen_S s hA] at hxN
    have hxeq : x * s.t * x⁻¹ = s.fr.z * s.t := by
      rcases hxN with h | h
      · exact absurd h hxconj
      · exact h
    have hzt : s.fr.z * s.t ∈ conjClass e.T₁ s.t := hxeq ▸ hxmem
    rintro w (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, by simp⟩
    · exact hzt
  have hsub2 : conjClass e.T₁ s.t ⊆ {s.t, s.fr.z * s.t} := by
    intro w hw
    have := hsub hw
    rwa [hN, yfd_tCoset_cen_S s hA] at this
  rw [le_antisymm hsub2 hpair, yfd_tCoset_cen_S s hA]

private lemma yfd_relIndex_T1_eq_two (hA : LFactsA s) (h31 : s.Fact31) (e : Setting3.Ext s) :
    s.T.relIndex e.T₁ = 2 := by
  letI := yfd_conjAct (G := G) e.T₁
  have hidx := MulAction.index_stabilizer ↥e.T₁ s.t
  have hstab : MulAction.stabilizer ↥e.T₁ s.t = s.T.subgroupOf e.T₁ := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change (x : G) * s.t * (x : G)⁻¹ = s.t ↔ (x : G) ∈ s.T
    rw [← s3_inf_H_T1 s e, Subgroup.mem_inf, Setting3.H,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have horb : (MulAction.orbit ↥e.T₁ s.t).ncard = 2 := by
    have h1 : MulAction.orbit ↥e.T₁ s.t = conjClass e.T₁ s.t := by
      ext w
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨(x : G), x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [h1, yfd_conjClass_T1 s hA h31 e, yfd_tCoset_cen_S s hA]
    exact Set.ncard_pair (yfd_z_mul_t_ne_t s hA).symm
  rw [hstab, horb] at hidx
  unfold Subgroup.relIndex
  exact hidx

theorem fusionDef_aut (hS : HRSetting G L) (h31 : s.Fact31)
    (hOut : (innerAut (L ⧸ center L)).index = 2) (hRT : s.R ≠ s.T) :
    SecProp s.T (zpowers s.t)
        (fun Y _ _ _ => ∀ P : Sylow 2 (MulAut (L ⧸ center L)), Nonempty (Y ≃* P)) ∧
      ∃ g ∈ s.T, g ∉ s.R ∧ ActsAs L g s.fr'.σ ∧ (g ^ 2 = 1 ∨ g ^ 2 = s.t) := by
  haveI hperf : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  let φ : ↥s.T →* MulAut (L ⧸ center L) := jOn L (s3_T_le_N s hS)
  have hker : φ.ker = (zpowers s.t).subgroupOf s.T := by
    change (jOn L (s3_T_le_N s hS)).ker = (zpowers s.t).subgroupOf s.T
    rw [ker_jOn L (s3_T_le_N s hS), ← Subgroup.inf_subgroupOf_right
      (Subgroup.centralizer (L : Set G)) s.T]
    congr 1
    rw [inf_comm, s3_T_inf_centralizer s h31]
  have hrange : φ.range = s.fr'.Sσ := by
    change (jOn L (s3_T_le_N s hS)).range = s.fr'.Sσ
    rw [range_jOn L (s3_T_le_N s hS), s3_jSub_T s hS hOut hRT]
  constructor
  · have hN : ((zpowers s.t).subgroupOf s.T).Normal := hker ▸ MonoidHom.normal_ker φ
    refine ⟨hN, ?_⟩
    intro P
    haveI : ((zpowers s.t).subgroupOf s.T).Normal := hN
    let Q : Sylow 2 (MulAut (L ⧸ center L)) :=
      s.facts.1.2.2.2.1.toSylow (by
        rw [← Subgroup.relIndex_top_right]
        exact s.facts.1.2.2.2.2)
    haveI : Finite (Sylow 2 (MulAut (L ⧸ center L))) := Sylow.finite_of_finiteIndex Q
    refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans ?_)⟩
    rw [hrange]
    exact Sylow.equiv Q P
  · have hσ : s.fr'.σ ∈ jSub L s.T := by
      rw [s3_jSub_T s hS hOut hRT]
      exact frame_sigma_mem_Sσ s.fr'
    obtain ⟨g, hgT, hgActs⟩ := (mem_jSub L).mp hσ
    have hgR : g ∉ s.R := by
      intro hgR
      have hσR : s.fr'.σ ∈ jSub L s.R := (mem_jSub L).mpr ⟨g, hgR, hgActs⟩
      rw [s3_jSub_R s] at hσR
      exact frame_sigma_not_mem_inner s.fr' s.facts.1 hOut
        (frame_S_le_inner s.fr' s.facts.1 hσR)
    refine ⟨g, hgT, hgR, hgActs, ?_⟩
    have h2acts : ActsAs L (g ^ 2) (s.fr'.σ ^ 2) := by
      have h := actsAs_mul L hgActs hgActs
      simpa [pow_two] using h
    rw [frame_sigma_sq s.fr' s.facts.1] at h2acts
    have h2cen : g ^ 2 ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp h2acts
    have h2zp : g ^ 2 ∈ zpowers s.t := by
      rw [← s3_T_inf_centralizer s h31]
      exact Subgroup.mem_inf.mpr ⟨s.T.pow_mem hgT 2, h2cen⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2zp
    have hmod := zpow_mod_orderOf s.t k
    rw [s.t_order] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      have hk1 : s.t ^ k = 1 := by
        rw [← hmod, show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0]
        simp
      rw [← hk, hk1]
    · right
      have hk1 : s.t ^ k = s.t := by
        rw [← hmod, show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1]
        simp
      rw [← hk, hk1]

theorem fusionDef_orbit (hA : LFactsA s) (h31 : s.Fact31) (e : Setting3.Ext s) :
    s.T.relIndex e.T₁ = 2 ∧ conjClass e.T₁ s.t = s.tCoset (cen s.fr.S) :=
  ⟨yfd_relIndex_T1_eq_two s hA h31 e, yfd_conjClass_T1 s hA h31 e⟩

theorem fusion3Def_of (h31 : Fusion31) (hZ : OddCentre) (hOut : OutTwo) : Fusion3Def :=
  fun G _ _ L hS hL s e =>
    ⟨fun hRT => fusionDef_aut s hS (h31 G L hS hL s) (hOut _ hL) hRT,
      fusionDef_orbit s (lfactsA_of_setting hS (hZ G L hS hL) s) (h31 G L hS hL s) e⟩

end CFSG.OddStandard.HigherRank.YamadaG23
