module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Noncyclic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5PairDerive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.FFThompson

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

theorem d2L34BetaMSideInput_of_pair_step
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hK : FFQuotientConstrained) (hP : FFPairStep) : D2L34BetaMSideInput :=
  d2L34BetaMSideInput_of_ff_case hFF hI59 ffThompsonInput ffSolvableInput
    (ffRankTwoInput_of_pairStep hP ffBaumStar) (ffNoncyclicInput_of_nodes hI59 hK hP ffBaumStar)

theorem d2L34BetaMSideInput_of_group_step
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hK : FFQuotientConstrained) (hN : D1NoXBlock) (hG : FFGroupStep) : D2L34BetaMSideInput :=
  d2L34BetaMSideInput_of_pair_step hFF hI59 hK (ffPairStep_of_groupStep hN hG)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
