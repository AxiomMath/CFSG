module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCGaps
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepE6
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepE7
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepE8
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley

section

theorem untwCrossRankStep_E6_all : UntwCrossRankStep Tag.E6 :=
  untwCrossRankStep_E6 cyclicSylowGap_E6_five

theorem untwCrossRankStep_E7_all : UntwCrossRankStep Tag.E7 :=
  untwCrossRankStep_E7 cyclicSylowGap_E7_five cyclicSylowGap_E7_eight cyclicSylowGap_E7_ten
    cyclicSylowGap_E7_twelve

theorem untwCrossRankStep_E8_all : UntwCrossRankStep Tag.E8 :=
  untwCrossRankStep_E8 cyclicSylowGap_E8_seven cyclicSylowGap_E8_nine cyclicSylowGap_E8_fourteen
    cyclicSylowGap_E8_eighteen

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
