module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.Assembly
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.FiveFixedDichotomy
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenRigid

public section

namespace CFSG.AGLEmbedding.TrialityTwo

theorem kFactThreeCentTrialityTwo_holds : KFactThreeCentTrialityTwo :=
  kFactThreeCentTrialityTwo_of fiveFixedDichotomy_holds sevenFixedRigid_holds

end CFSG.AGLEmbedding.TrialityTwo
