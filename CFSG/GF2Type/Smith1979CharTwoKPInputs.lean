module

public import CFSG.GF2Type.Smith1979CharTwoKPWidths
public import CFSG.GF2Type.Smith1979W3.WidthThreeHolds
public import CFSG.GF2Type.Smith1979.WidthFourKPLayer
public import CFSG.GF2Type.Smith1979.WidthSixKPHolds
public import CFSG.Quasithin.H13.AS91ResHolds823
public import CFSG.Quasithin.H13.AS91Sec8V1Holds

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Open

section Certs


theorem smith1979CharTwoKP_of_widthFour (hTh : Smith1979.ParrottThKP)
    (hQ2 : Smith1979.WidthFourOmegaPlusLayerFalse) : Smith1979StatementCharTwoKP :=
  smith1979CharTwoKP_of_widthsKP Smith1979W3.smith1979WidthThreeCharTwoKP_holds
    (Smith1979.smith1979WidthsFourSixCharTwoKP_of_widths
      (Smith1979.smith1979WidthFourCharTwoKP_of_th_layer hTh hQ2)
      (Smith1979.smith1979WidthSixCharTwoKP_of_inputAS91
        (Quasithin.H13.AS91.inputAS91_of_stmt8_2_3 Quasithin.H13.AS91.stmt8_2_3_holds)))

end Certs

end CFSG.GF2Type
