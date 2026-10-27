module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614DeltaDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614DOGCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

theorem pieceDeltaOmegaL34_holds : PieceDeltaOmegaL34 := by
  intro k278 kL kT29 kNC kQ G _ _ P M x z H S hyp hnα Q₀ hQ₀H hQ₀p hBQ₀ q hqQ₀ hq3
  by_contra hqB
  obtain ⟨Q, K, hD⟩ := P614DOG.exists_data278 k278 hyp hQ₀H hQ₀p hBQ₀ hqQ₀ hq3 hqB
  exact P614DOG.false_of_data278 kL kT29 kNC kQ hyp hnα hD

theorem pieceDeltaOmega_holds_of_l34 (k278 : KFact278L34) (kL : KFactL34DiagGen) :
    PieceDeltaOmega :=
  pieceDeltaOmega_of_l34 pieceDeltaOmegaL34_holds k278 kL

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
