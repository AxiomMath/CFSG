module

public import CFSG.GF2Type.Smith1979.WidthFourKPAssembly
public import CFSG.LargeExtraspecial.DWW4.ReducibleWidthFourFinal
public import CFSG.GF2Type.Smith1979.WidthFourKP.Triality

public section

namespace CFSG.GF2Type.Smith1979

theorem smith1979WidthFourCharTwoKP_of_th_omega
    (hTh : ParrottThKP) (hΩ : WidthFourOmegaCase) : Smith1979WidthFourCharTwoKP :=
  smith1979WidthFourCharTwoKP_of_leaves CFSG.LargeExtraspecial.DW.dw37WidthFourStatement_holds
    widthFourTrialityCase_holds hTh hΩ

end CFSG.GF2Type.Smith1979
