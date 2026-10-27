module

public import CFSG.GF2Type.Smith1979CharTwoKPInputs
public import CFSG.GF2Type.Smith1979.ParrottThHolds
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.LayerFalse

public section

namespace CFSG.GF2Type

theorem Smith1979.smith1979WidthFourCharTwoKP_holds :
    Smith1979.Smith1979WidthFourCharTwoKP :=
  Smith1979.smith1979WidthFourCharTwoKP_of_th_layer Smith1979.parrottThKP_holds
    Smith1979.OmegaPlus.widthFourOmegaPlusLayerFalse_holds

theorem smith1979WidthsFourSixCharTwoKP_holds :
    Smith1979WidthsFourSixCharTwoKP :=
  Smith1979.smith1979WidthsFourSixCharTwoKP_of_widths Smith1979.smith1979WidthFourCharTwoKP_holds
    (Smith1979.smith1979WidthSixCharTwoKP_of_inputAS91
      (Quasithin.H13.AS91.inputAS91_of_stmt8_2_3 Quasithin.H13.AS91.stmt8_2_3_holds))

theorem smith1979CharTwoKP_holds :
    Smith1979StatementCharTwoKP :=
  smith1979CharTwoKP_of_widthFour Smith1979.parrottThKP_holds
    Smith1979.OmegaPlus.widthFourOmegaPlusLayerFalse_holds

end CFSG.GF2Type
