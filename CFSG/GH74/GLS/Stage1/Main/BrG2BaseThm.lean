module

public import CFSG.GH74.GLS.Stage1.Main.BrG2Base
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylFwd

public section

namespace CFSG.GH74.GLS.Stage1.Main

theorem baseBridgeG2_thm :
    BaseBridgeG2 :=
  baseBridgeG2_of_shape fun Gs _ _ p f hp hp2 hf hL S' =>
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.g2_sylow_shapeConds_fwd Gs p f hp hp2 hf hL S'

end CFSG.GH74.GLS.Stage1.Main
