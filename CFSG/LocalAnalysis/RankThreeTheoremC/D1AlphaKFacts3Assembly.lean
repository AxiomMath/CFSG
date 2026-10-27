module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Small
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Onan
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Out

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

theorem d1AlphaKFacts3_of_datum
    (hList : KFactAlphaListM3) (hOn : ONanSylowThreeDatum) (hLift : KFactSL3LiftGen) :
    D1AlphaKFacts3 :=
  ⟨hList, kFactAlphaSmallAut3, kFactAlphaOnan3_of_datum hOn, kFactSL3OutNormalSylow, hLift⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
