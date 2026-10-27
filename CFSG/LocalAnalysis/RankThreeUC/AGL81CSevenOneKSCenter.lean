module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRankHolds

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C


theorem kFactCenterRankFive_holds : KFactCenterRankFive := by
  intro X _ _ hK L hL p hp hp5 hdvd
  have hq : CFSG.Open.IsQuasisimple ↥L := ⟨Group.isPerfect_def.mp hL.1.1, hL.1.2.1⟩
  have hcat : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) := by
    have hK' : CFSG.KCore.KGroupNonab @CFSG.Open.IsCatalogGroup X := hK
    let L' : Subgroup X := (Subgroup.center ↥L).map L.subtype
    have hle : L' ≤ L := Subgroup.map_subtype_le _
    have heq : L'.subgroupOf L = Subgroup.center ↥L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    haveI : (L'.subgroupOf L).Normal := heq ▸ inferInstance
    let e : (↥L ⧸ L'.subgroupOf L) ≃* (↥L ⧸ Subgroup.center ↥L) :=
      QuotientGroup.quotientMulEquivOfEq heq
    haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
    haveI : IsSimpleGroup (↥L ⧸ L'.subgroupOf L) := e.isSimpleGroup
    have hnab : ∃ a b : ↥L ⧸ L'.subgroupOf L, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hL.1.2.2
      exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
    obtain ⟨i, ⟨φ⟩⟩ := hK' L L' hle inferInstance hnab
    exact ⟨i, ⟨e.symm.trans φ⟩⟩
  have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SchurRank.schurMultiplierRankFact_holds
    p hp hp5 ↥L hq hcat hdvd
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
