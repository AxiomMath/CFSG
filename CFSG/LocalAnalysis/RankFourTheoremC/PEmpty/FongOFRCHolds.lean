module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwFinal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwG2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwF4

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

section


theorem outerFixedRankCross_holds :
    ∀ t, OuterFixedRankCrossAt t :=
  outerFixedRankCross_holds_of_ree outerFixedRankCrossAt_twistedG2 outerFixedRankCrossAt_twistedF4

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
