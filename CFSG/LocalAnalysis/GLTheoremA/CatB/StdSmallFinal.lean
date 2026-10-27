module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdSmallMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section Final


theorem stdSubSmallAt_of_covers (G : Type) [Group G] [Finite G] (hcov : StdSubCoverAt G)
    (hinn4 : StdSubInnerD4At G) : StdSubSmallAt G :=
  stdSubSmallAt_of_cover_facts hcov hinn4 (CatB.rank23At_holds G)
    (fun _ _ _ h => D4XF.d4two_rank4 h)

end Final

end CFSG.LocalAnalysis.GLTheoremA
