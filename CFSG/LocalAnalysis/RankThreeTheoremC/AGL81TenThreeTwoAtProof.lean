module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81JOneSolvPrimes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem agl81TenThreeTwoAt {G : Type} [Group G] [Finite G] : AGL81TenThreeTwoAt G :=
  fun _ _ _ _ _ _ _ _ _ _ hs _ hq hd => prime_eq_of_dvd_card_jOne hs hq hd

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
