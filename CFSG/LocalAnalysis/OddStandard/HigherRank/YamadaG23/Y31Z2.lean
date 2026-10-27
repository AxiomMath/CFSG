module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRel

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private theorem jOn_cen_T_le_Z (hS : HRSetting G L)
    (hOut : (innerAut (L ⧸ center L)).index = 2) (hRT : s.R ≠ s.T) {c : ↥s.T}
    (hc : c ∈ (cen s.T).subgroupOf s.T) :
    jOn L (s3_T_le_N s hS) c ∈ s.fr'.Z := by
  have hcenSσ : cen s.fr'.Sσ = s.fr'.Z := s.facts.2.2.2.2.1.1.1
  have hrange : (jOn L (s3_T_le_N s hS)).range = s.fr'.Sσ := by
    rw [range_jOn L (s3_T_le_N s hS), s3_jSub_T s hS hOut hRT]
  have hcC : (c : G) ∈ centralizer (s.T : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).2
  have hαS : jOn L (s3_T_le_N s hS) c ∈ s.fr'.Sσ := by
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨c, rfl⟩
  have hαC : jOn L (s3_T_le_N s hS) c ∈
      centralizer (s.fr'.Sσ : Set (MulAut (L ⧸ center L))) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro β hβ
    have hβ' : β ∈ (jOn L (s3_T_le_N s hS)).range := by rw [hrange]; exact hβ
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hβ'
    rw [← hd]
    have hcd : (d : G) * (c : G) = (c : G) * (d : G) :=
      (Subgroup.mem_centralizer_iff.mp hcC) (d : G) d.2
    have h1 : ActsAs L ((c : G) * (d : G))
        (jOn L (s3_T_le_N s hS) c * jOn L (s3_T_le_N s hS) d) :=
      actsAs_mul L (jOn_actsAs L (s3_T_le_N s hS) c) (jOn_actsAs L (s3_T_le_N s hS) d)
    have h2 : ActsAs L ((c : G) * (d : G))
        (jOn L (s3_T_le_N s hS) d * jOn L (s3_T_le_N s hS) c) := by
      rw [← hcd]
      exact actsAs_mul L (jOn_actsAs L (s3_T_le_N s hS) d)
        (jOn_actsAs L (s3_T_le_N s hS) c)
    exact (actsAs_unique L h1 h2).symm
  have hmem : jOn L (s3_T_le_N s hS) c ∈ cen s.fr'.Sσ :=
    Subgroup.mem_inf.mpr ⟨hαS, hαC⟩
  rwa [hcenSσ] at hmem

theorem s3_sq_mem_Q_of_Z2 (hS : HRSetting G L)
    (hOut : (innerAut (L ⧸ center L)).index = 2) (hRT : s.R ≠ s.T) {x : G} (hx : x ∈ s.T)
    (hx2 : ∀ y ∈ s.T, x * y * x⁻¹ * y⁻¹ ∈ cen s.T) :
    x ^ 2 ∈ s.T ⊓ centralizer (L : Set G) := by
  haveI hperf : Group.IsPerfect ↥L := isPerfect_of_hrSetting (L := L) hS
  let φ : ↥s.T →* MulAut (L ⧸ center L) := jOn L (s3_T_le_N s hS)
  have hrange : φ.range = s.fr'.Sσ := by
    change (jOn L (s3_T_le_N s hS)).range = s.fr'.Sσ
    rw [range_jOn L (s3_T_le_N s hS), s3_jSub_T s hS hOut hRT]
  have hcenSσ : cen s.fr'.Sσ = s.fr'.Z := s.facts.2.2.2.2.1.1.1
  have hzser2 : zSeries 2 s.fr'.Sσ = cen s.fr'.B := s.facts.2.2.2.2.1.1.2.1
  have hcenB : cen s.fr'.B = closure ({s.fr'.b₁ * s.fr'.b₂, s.fr'.z} :
      Set (MulAut (L ⧸ center L))) := s.facts.2.2.2.1.2.2.1.1
  have hsrel : SRel s.fr'.toSFrame := srel_of_fact11 s.fr' s.facts.1
  have hb1b2 : Commute s.fr'.b₁ s.fr'.b₂ :=
    commutatorElement_eq_one_iff_commute.mp hsrel.b1b2
  have hb1sq : s.fr'.b₁ ^ 2 = s.fr'.z := rfl
  have hb2sq : s.fr'.b₂ ^ 2 = s.fr'.z := hsrel.b2_sq
  have hzsq : s.fr'.z ^ 2 = 1 := hsrel.z_sq
  let α : MulAut (L ⧸ center L) := φ ⟨x, hx⟩
  have hact_x : ActsAs L x α := jOn_actsAs L (s3_T_le_N s hS) ⟨x, hx⟩
  have hαS : α ∈ s.fr'.Sσ := by
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
  have hcommZ : ∀ y ∈ s.fr'.Sσ, ⁅α, y⁆ ∈ s.fr'.Z := by
    intro y hy
    have hy' : y ∈ (jOn L (s3_T_le_N s hS)).range := by rw [hrange]; exact hy
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hy'
    rw [← hd]
    have hcd : (⁅(⟨x, hx⟩ : ↥s.T), d⁆ : ↥s.T) ∈ (cen s.T).subgroupOf s.T := by
      rw [Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def] using hx2 (d : G) d.2
    have hmemZ := jOn_cen_T_le_Z s hS hOut hRT hcd
    have hmap : jOn L (s3_T_le_N s hS) (⁅(⟨x, hx⟩ : ↥s.T), d⁆ : ↥s.T) =
        ⁅α, jOn L (s3_T_le_N s hS) d⁆ :=
      map_commutatorElement (jOn L (s3_T_le_N s hS)) (⟨x, hx⟩ : ↥s.T) d
    rw [hmap] at hmemZ
    exact hmemZ
  have hαZ2 : α ∈ zSeries 2 s.fr'.Sσ := by
    show α ∈ (Subgroup.upperCentralSeries ↥s.fr'.Sσ 2).map s.fr'.Sσ.subtype
    rw [Subgroup.mem_map]
    refine ⟨⟨α, hαS⟩, ?_, rfl⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
    intro z
    have hcZ : ((⁅(⟨α, hαS⟩ : ↥s.fr'.Sσ), y⁆ : ↥s.fr'.Sσ) :
        MulAut (L ⧸ center L)) ∈ s.fr'.Z := by
      have h := hcommZ (y : MulAut (L ⧸ center L)) y.2
      simpa [commutatorElement_def] using h
    have hcZ' : ((⁅(⟨α, hαS⟩ : ↥s.fr'.Sσ), y⁆ : ↥s.fr'.Sσ) :
        MulAut (L ⧸ center L)) ∈ cen s.fr'.Sσ := by
      rw [hcenSσ]
      exact hcZ
    have hcomm := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcZ').2)
      (z : MulAut (L ⧸ center L)) z.2
    exact Subtype.ext hcomm
  have hαmem : α ∈ closure ({s.fr'.b₁ * s.fr'.b₂, s.fr'.z} :
      Set (MulAut (L ⧸ center L))) := by
    have h := hαZ2
    rw [hzser2, hcenB] at h
    exact h
  have hgz : Commute (s.fr'.b₁ * s.fr'.b₂) s.fr'.z :=
    (((Commute.refl s.fr'.b₁).mul_right hb1b2).symm).pow_right 2
  have hb1b2sq : (s.fr'.b₁ * s.fr'.b₂) ^ 2 = 1 := by
    calc (s.fr'.b₁ * s.fr'.b₂) ^ 2 = s.fr'.b₁ ^ 2 * s.fr'.b₂ ^ 2 := hb1b2.mul_pow 2
      _ = s.fr'.z * s.fr'.z := by rw [hb1sq, hb2sq]
      _ = 1 := by simpa [pow_two] using hzsq
  have hcomm_all : ∀ u ∈ closure ({s.fr'.b₁ * s.fr'.b₂, s.fr'.z} :
      Set (MulAut (L ⧸ center L))), ∀ v ∈ closure ({s.fr'.b₁ * s.fr'.b₂, s.fr'.z} :
      Set (MulAut (L ⧸ center L))), u * v = v * u := by
    have hle : closure ({s.fr'.b₁ * s.fr'.b₂, s.fr'.z} :
        Set (MulAut (L ⧸ center L))) ≤
        centralizer (closure ({s.fr'.b₁ * s.fr'.b₂, s.fr'.z} :
          Set (MulAut (L ⧸ center L)))) := by
      rw [Subgroup.closure_le]
      intro w hw
      rw [Subgroup.centralizer_closure]
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw hv
      rcases hw with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hgz.symm.eq
      · exact hgz.eq
      · rfl
    intro u hu v hv
    exact (Subgroup.mem_centralizer_iff.mp (hle hu) v hv).symm
  have hα2 : α ^ 2 = 1 := by
    have hprop : ∀ u ∈ closure ({s.fr'.b₁ * s.fr'.b₂, s.fr'.z} :
        Set (MulAut (L ⧸ center L))), u ^ 2 = 1 := by
      intro u hu
      refine Subgroup.closure_induction (p := fun u _ => u ^ 2 = 1) ?_ ?_ ?_ ?_ hu
      · intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact hb1b2sq
        · exact hzsq
      · exact one_pow 2
      · intro w v hw hv ihw ihv
        have hwv : w * v = v * w := hcomm_all w hw v hv
        calc (w * v) ^ 2 = w * v * w * v := by rw [pow_two]; group
          _ = w * (v * w) * v := by group
          _ = w * (w * v) * v := by rw [hwv]
          _ = w ^ 2 * v ^ 2 := by rw [pow_two, pow_two]; group
          _ = 1 := by rw [ihw, ihv, mul_one]
      · intro w hw ihw
        rw [inv_pow, ihw, inv_one]
    exact hprop α hαmem
  have hacts : ActsAs L (x ^ 2) (1 : MulAut (L ⧸ center L)) := by
    have h := actsAs_mul L hact_x hact_x
    have hαα : α * α = 1 := by rw [← pow_two, hα2]
    rw [hαα] at h
    simpa [pow_two] using h
  have hcenL : x ^ 2 ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hacts
  exact Subgroup.mem_inf.mpr ⟨s.T.pow_mem hx 2, hcenL⟩

end CFSG.OddStandard.HigherRank.YamadaG23
