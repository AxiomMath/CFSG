module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K7145Index
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K7145Comp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutMain

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor


theorem K7145_holds : K7145 := by
  intro X _ _ hK p hp hp2 L hL hq hr x hx hxL
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  obtain ⟨N, hNn, hNp, hNi⟩ := (kFactI713Out_holds p hp hp2 (↥L ⧸ Subgroup.center ↥L)
    inferInstance (K7145Proof.quotient_center_nonabelian hq)
    (K7145Proof.isCatalogGroup_quotient_center hK L hq)
    (K7145Proof.pRank_quotient_center_le_one hp hp2 L hr)).2
  have hψ : K7145Proof.outerAction L x ≠ 1 := fun h =>
    hxL (K7145Proof.mem_sup_centralizer_of_outerAction_eq_one L h)
  exact K7145Proof.exists_normal_index_prime_of_outer (K7145Proof.outerAction L) N hp hNp hNi
    hx hψ

end CFSG.LocalAnalysis.RankThreeUC.S15
