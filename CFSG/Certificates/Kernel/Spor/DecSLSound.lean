module

public import Certificates.Data.Kernel.Spor.DecSL
public import CFSG.Sporadic.ONOddCore.LocalAutPayload
import CFSG.Certificates.Kernel.Spor.DecSLProved

public section

namespace CFSG.KS.DecSL

theorem natsOf_ofList {cs : List Char} (h : digitsSLOK cs = true) :
    CFSG.Sporadic.ONOddCore.natsOf (String.ofList cs) = natsSL cs :=
  natsOf_ofList_proved h

end CFSG.KS.DecSL

end
