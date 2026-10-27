module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B1

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

theorem sylowCentralizer_le_centralizer_plane {P : Sylow 3 G} {x z : G}
    (hz : SmallRankCentral P z) :
    (P : Subgroup G) ⊓ centralizer ({x} : Set G) ≤
      centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
  · rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.mp (mem_inf.mp hl).2
  · exact Subgroup.centralizer_le (fun _ hg => (mem_inf.mp hg).1) hz.centralizes

theorem hasNormalPComplement_centralizer_of_inf (hS : Setting G) (hU0 : FullCoreLocal G)
    {P : Sylow 3 G} {M : Subgroup G} (hsit : SmallRankSituation G 3 P M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z)
    (hMC : CFSG.HasNormalPComplement 3 ↥(M ⊓ centralizer ({x} : Set G))) :
    CFSG.HasNormalPComplement 3 ↥(centralizer ({x} : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hCx : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2 := by
    by_contra h
    push Not at h
    exact hsit.largeObstruction_empty x
      ⟨hPM hx.mem, hx.ne_one, hx.pow_eq_one, by omega, hx.not_centralizer_le⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  set Px : Subgroup G := (P : Subgroup G) ⊓ C with hPxdef
  set B : Subgroup G := zpowers x ⊔ zpowers z with hBdef
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hNB : normalizer (B : Set G) ≤ M := normalizer_plane_le hS hU0 hsit hx hz
  have hPxC : Px ≤ C := inf_le_right
  have hPx3 : IsPGroup 3 Px := P.isPGroup'.to_le inf_le_left
  have hBC : B ≤ C := sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hz.centralizes x hx.mem).symm))
  have hBPx : B ≤ Px := le_inf hpl.isIsolatedPlane.1 hBC
  have hPxCB : Px ≤ centralizer (B : Set G) := sylowCentralizer_le_centralizer_plane hz
  have hΩ : ∀ q ∈ Px, q ^ 3 = 1 → q ∈ B := fun q hq hq3 =>
    hpl.mem_of_mem_centralizer q (hPxCB hq) hq3
  have hnorm : ∀ Y : Subgroup G, B ≤ Y → Y ≤ Px →
      normalizer (Y : Set G) ≤ normalizer (B : Set G) := by
    intro Y hBY hYPx
    have key : ∀ h ∈ normalizer (Y : Set G), ∀ b ∈ B, h * b * h⁻¹ ∈ B := by
      intro h hh b hb
      have h1 : h * b * h⁻¹ ∈ Y := (mem_normalizer_iff.mp hh b).mp (hBY hb)
      refine hΩ _ (hYPx h1) ?_
      rw [conj_pow, hpl.isElemAbelian.2 b hb, mul_one, mul_inv_cancel]
    intro g hg
    rw [mem_normalizer_iff]
    intro b
    refine ⟨key g hg b, fun hb => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hb
    simpa [mul_assoc] using this
  have hPQ3 : IsPGroup 3 ↥(Px.subgroupOf C) := hPx3.comap_subtype
  set PQ : Sylow 3 ↥C := hPQ3.toSylow hx.sylow_centralizer with hPQdef
  have hPQmap : (PQ : Subgroup ↥C).map C.subtype = Px := by
    rw [hPQdef, IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPxC]
  have hPxrank : CFSG.pRank 3 ↥Px = 2 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    refine le_antisymm ((CFSG.SectionRank.pRank_mono (by norm_num) hPxC).trans hCx) ?_
    exact CFSG.SectionRank.le_pRank (by norm_num) hBPx hpl.isElemAbelian hpl.card_eq
  have hBJ : B ≤ (CFSG.elemThompson ↥Px 3).map Px.subtype := by
    have hmemfam : B.subgroupOf Px ∈ CFSG.elemThompsonFamily ↥Px 3 := by
      refine ⟨?_, ?_⟩
      · rw [CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff]
        refine ⟨fun a ha b hb => Subtype.ext ?_, fun a ha => Subtype.ext ?_⟩
        · show (a : G) * b = b * a
          exact congrArg Subtype.val (hpl.isElemAbelian.1.is_comm.comm ⟨(a : G), ha⟩ ⟨(b : G), hb⟩)
        · show (a : G) ^ 3 = 1
          exact hpl.isElemAbelian.2 _ ha
      · rw [hPxrank, ← hpl.card_eq]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBPx).toEquiv
    have hle : B.subgroupOf Px ≤ CFSG.elemThompson ↥Px 3 := le_sSup hmemfam
    have := Subgroup.map_mono (f := Px.subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBPx] at this
  have hBZ : B ≤ (center ↥Px).map Px.subtype := by
    intro b hb
    rw [CFSG.RankThree.Coprime.mem_map_center_iff]
    exact ⟨hBPx hb, fun l hl => (mem_centralizer_iff.mp (hPxCB hl) b hb).symm⟩
  have hMC' : ∀ Y : Subgroup G, Y ≤ normalizer (B : Set G) →
      CFSG.HasNormalPComplement 3 ↥(C ⊓ Y) := by
    intro Y hY
    refine CFSG.hasNormalPComplement_of_le 3 ?_ hMC
    intro g hg
    exact ⟨hNB (hY (mem_inf.mp hg).2), (mem_inf.mp hg).1⟩
  have key := CFSG.RankThree.Coprime.hyp_subgroup 3 C (PQ : Subgroup ↥C) ?_ ?_
  · exact CFSG.RankThree.Coprime.thompson_elementary_normal_p_complement (by norm_num) PQ
      key.1 key.2
  · rw [hPQmap]
    exact hMC' _ ((Subgroup.centralizer_le_normalizer _).trans
      (hnorm _ hBZ (Subgroup.map_subtype_le _)))
  · rw [hPQmap]
    exact hMC' _ (hnorm _ hBJ (Subgroup.map_subtype_le _))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B1
