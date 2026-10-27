module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Leaves3
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeOrFiveDvd
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporVacuous3
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLieCharRankProof
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactSeitzRankThree
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInner
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

section Core

theorem D2KFactLeavesCore.toLeaves (h : D2KFactLeavesCore) (hsec : SporSectionFacts3) :
    D2KFactLeaves :=
  ⟨h, aschbacherLocalCGTBlock_proved,
    CFSG.AGLEmbedding.asc81bEightFour_of_cgtBlock aschbacherLocalCGTBlock_proved,
    CFSG.AGLEmbedding.asc81bEightFive_of_factorization aschbacherLocalFactorization_proved,
    CFSG.AGLEmbedding.asc81bEightSix_of_bhs bhsLocalCStar_proved,
    CFSG.AGLEmbedding.kFactParabolicThree, CFSG.AGLEmbedding.TwoGenInner.kFactTwoGenInner,
    CFSG.AGLEmbeddingD2.kFactLieCharRank, CFSG.AGLEmbedding.kFactCatalogSchreier,
    CFSG.AGLEmbeddingD2.kFactSeitzRankThreeExceptions, hsec,
    CFSG.AGLEmbedding.kFactThreeOrFiveDvd, d2SporadicVacuous3_of_certificates⟩

end Core

end CFSG.LocalAnalysis.RankThreeTheoremC
