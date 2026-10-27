module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3LayerSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.L34CentralTwo
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.InvariantTwoInCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.ComponentClassification.PSL3Four

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaInvariantTwoInCore3_of_kfact
    (hK : KFactL34CentralTwo) :
    D2L34BetaInvariantTwoInCore3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax X hXHM hX2 hAX
  exact D2L34BetaConf3.le_glbPrimeCore_of_invariant_two hK ctx.conf hXHM hX2 hAX

theorem d2L34BetaInvariantTwoInCore3_proved :
    D2L34BetaInvariantTwoInCore3 G :=
  d2L34BetaInvariantTwoInCore3_of_kfact kFactL34CentralTwo

end CFSG.LocalAnalysis.RankThreeTheoremC
