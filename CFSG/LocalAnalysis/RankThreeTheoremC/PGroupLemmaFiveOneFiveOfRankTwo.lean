module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFive
import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFiveP2
import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupLemmaFiveOneFiveP3
import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupRankTwoCharSubgroupOf

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

theorem pGroupLemmaFiveOneFive_of_rankTwo (h1 : PGroupRankTwoCharSubgroup G) :
    PGroupLemmaFiveOneFive G :=
  pGroupLemmaFiveOneFive_of h1 pGroupExtraspecialNormalizer pGroupExtraspecialOmegaOne

theorem pGroupLemmaFiveOneFive : PGroupLemmaFiveOneFive G :=
  pGroupLemmaFiveOneFive_of_rankTwo (pGroupRankTwoCharSubgroup (G := G))

theorem agl81ElevenNineGammaFive : AGL81ElevenNineGammaFive G :=
  agl81ElevenNineGammaFive_of pGroupLemmaFiveOneFive

end CFSG.LocalAnalysis.RankThreeTheoremC
