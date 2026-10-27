module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Only
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.TwoLocalN1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

variable {G : Type} [Group G] [Finite G]

theorem D2L34BetaConf3.isSylowTwoOf_top_and_card [D2Amb3 G]
    (hFF : CitedFFL34BestOffender) {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {T U : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M))
    (hU : IsSylowTwoOf U H) (_hTU : T ≤ U) :
    IsSylowTwoOf U ⊤ ∧ Nat.card U = 8 * Nat.card T :=
  ⟨D2L34BetaConf3.isSylowTwoOf_top_of_isSylowTwoOf hFF hc hstr hOnly hU,
    D2L34BetaConf3.card_eq_eight_mul hc hT hU⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
