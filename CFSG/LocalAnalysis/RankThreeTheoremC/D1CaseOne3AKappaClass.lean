module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Competitor

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmall3Data.d1Kappa_le_card (hd : D1OneSmall3Data p P M H R Rbar K) :
    Hyp111.d1Kappa p M H ≤ Nat.card K :=
  Subgroup.card_le_of_le (iSup₂_le fun _ hL => Hyp111.le_of_not_le_compCore hd.toCore hL.1 hL.2)

end Competitor

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.RankThreeTheoremC
