module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Final
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411

public section

namespace CFSG.AGLEmbedding


theorem kFactChevTwoOuterGen_of_certificates : KFactChevTwoOuterGen :=
  CFSG.LocalAnalysis.RankThreeTheoremC.kFactChevTwoOuterGen_of_parts
    CFSG.LocalAnalysis.RankThreeTheoremC.kFactChevTwoOuterNormal
    ChevOuter.kFactChevTwoOuterGen3D42 ChevOuterD48.kFactChevTwoOuterGen3D48
    ChevOuter.kFactChevTwoOuterGenU38

end CFSG.AGLEmbedding
