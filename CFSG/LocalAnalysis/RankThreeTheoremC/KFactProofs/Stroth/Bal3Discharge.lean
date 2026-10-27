module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Small
public import CFSG.RankThree.PartOne.TCB.SchreierFinal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.LocalAnalysis.RankThreeTheoremC

theorem bal3ThreeCovers_of_wide (h : KFactAlphaListM3Wide) : Bal3ThreeCovers := h


theorem bal3SmallCards_holds : Bal3SmallCards := kFactAlphaSmallAut3Card

theorem bal3OnanComm_of_datum (h : ONanSylowThreeDatum) : Bal3OnanComm :=
  kFactAlphaOnan3Comm_of_datum h

theorem bal3KFacts_of_open (hK : SchurMultiplierRankFact) (hW : KFactAlphaListM3Wide)
    (hZ : Bal3ThreeCenter) (hO : ONanSylowThreeDatum) (hL : Bal3ThreeSL3)
    (h294 : Input29_4Rank3) : Bal3KFacts :=
  bal3KFacts_of_cover_inputs hK
    ⟨bal3ThreeCovers_of_wide hW, hZ, bal3SmallCards_holds, bal3OnanComm_of_datum hO, hL,
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds⟩ h294

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
