module

public import Certificates.Data.Kernel.DecText
public import Certificates.Data.CFSGNative.Fi23.CentralizerData
import CFSG.Certificates.Kernel.DecTextProved

public section

namespace CFSG.KC.DecText

theorem natsOf_ofList {cs : List Char} (h : digitsOK cs = true) :
    CFSG.Sporadic.Fi23.Native.natsOf (String.ofList cs) = (natsK cs).toArray :=
  natsOf_ofList_proved h

end CFSG.KC.DecText

end
