module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MsideFinal

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding

theorem d2L34BetaMSide_of_O (h : D2L34BetaMSideO) : D2L34BetaMSide :=
  h

theorem d2L34BetaMSide_of_ff
    (hFF : CitedFFL34BestOffender) (hin : D2L34BetaMSideInput)
    (hnc : D2L34BetaMSideNonConstrainedInput) : D2L34BetaMSide :=
  d2L34BetaMSide_of_O (d2L34BetaMSideO_of_ff hFF hin hnc)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
