module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.E81
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFSideInput

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

theorem ffThompsonInput :
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.FFThompsonInput := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll T hT hNT
  exact D2L34BetaConf.thompsonJ_not_le_centralizer hc hstr hAll hT hNT

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
