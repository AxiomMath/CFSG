module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepAll
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepG2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCStepF4

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint.Chevalley

section

theorem outerFixedRankCross_holds_of_twisted
    (h2E6 : OuterFixedRankCrossAt .twistedE6) (h3D4 : OuterFixedRankCrossAt .trialityD4)
    (h2G2 : OuterFixedRankCrossAt .twistedG2) (h2F4 : OuterFixedRankCrossAt .twistedF4) :
    ∀ t, OuterFixedRankCrossAt t := by
  refine outerFixedRankCross_holds_of fun t _ => ?_
  cases t
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · trivial
  · exact untwCrossRankStep_G2
  · exact untwCrossRankStep_F4
  · exact untwCrossRankStep_E6_all
  · exact untwCrossRankStep_E7_all
  · exact untwCrossRankStep_E8_all
  · exact h2E6
  · exact h3D4
  · trivial
  · exact h2G2
  · exact h2F4
  · trivial

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
