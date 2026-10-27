module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCDispatch
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwE6Desc
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwE6Step
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTriD4Desc
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTriD4Step
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTriPhi1

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag)

section


theorem outerFixedRankCrossAt_twistedE6 : OuterFixedRankCrossAt .twistedE6 :=
  outerFixedRankCrossAt_twistedE6_of_step twE6CrossRankStep

theorem outerFixedRankCrossAt_trialityD4 : OuterFixedRankCrossAt .trialityD4 :=
  outerFixedRankCrossAt_trialityD4_of_step (triD4CrossRankStep two_le_pRank_triality_phi1_general)

theorem outerFixedRankCross_holds_of_ree
    (h2G2 : OuterFixedRankCrossAt .twistedG2) (h2F4 : OuterFixedRankCrossAt .twistedF4) :
    ∀ t, OuterFixedRankCrossAt t :=
  outerFixedRankCross_holds_of_twisted outerFixedRankCrossAt_twistedE6
    outerFixedRankCrossAt_trialityD4 h2G2 h2F4

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
