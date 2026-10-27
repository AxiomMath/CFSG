module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEven
public import CFSG.RankThree.PartTwo.KFacts.KS44Sz

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup

section Holds

theorem kFactSuzukiThreeFree_holds : KFactSuzukiThreeFree := by
  intro J _ _ hs hna hK h3
  haveI : IsSimpleGroup J := hs
  have hab : ∃ a b : J, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hna h
  have hcat : CFSG.Assembly.InCatalog J :=
    hK.isCatalogGroup_of_surjective ⊤ hab (Subgroup.topEquiv (G := J)).toMonoidHom
      (Subgroup.topEquiv (G := J)).surjective
  exact CFSG.RankThree.PartTwo.KFacts.kpSz J hab hcat h3

theorem kFactFieldAutEvenAt_three_holds : KFactFieldAutEvenAt 3 :=
  kFactFieldAutEvenAt_three_of_suzuki kFactSuzukiThreeFree_holds

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
