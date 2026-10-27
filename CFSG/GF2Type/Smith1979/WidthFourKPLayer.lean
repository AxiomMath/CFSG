module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus
public import CFSG.GF2Type.Smith1979.WidthFourKP.MinusCentral.Main
public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.Exclusion
public import CFSG.GF2Type.Smith1979.WidthFourKPReduced

public section

namespace CFSG.GF2Type.Smith1979

theorem widthFourOmegaCase_of_layer
    (hQ2 : WidthFourOmegaPlusLayerFalse) : WidthFourOmegaCase :=
  widthFourOmegaCase_of_cases (widthFourOmegaMinus_of_central widthFourSwapFalse
      W4MinusC.widthFourOmegaMinusCentral_holds) (widthFourOmegaPlus_of_layer hQ2)
    widthFourOmegaTrialityFalse

theorem smith1979WidthFourCharTwoKP_of_th_layer
    (hTh : ParrottThKP) (hQ2 : WidthFourOmegaPlusLayerFalse) : Smith1979WidthFourCharTwoKP :=
  smith1979WidthFourCharTwoKP_of_th_omega hTh (widthFourOmegaCase_of_layer hQ2)

end CFSG.GF2Type.Smith1979

end
