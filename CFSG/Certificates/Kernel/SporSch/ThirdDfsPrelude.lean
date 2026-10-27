
module

public import CFSG.Certificates.Kernel.SporSch.ThirdDfsBase
import all CFSG.Certificates.Kernel.SporSch.ThirdDfsBase

public import CFSG.Assembly.Defs
public import CFSG.Certificates.Kernel.SporSch.ThirdChainHBase
public import Certificates.Data.CFSGNative.Schreier.SetOrbit

@[expose] public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

section Count

variable (h : ThirdFactsH)
include h

end Count

end CFSG.Sporadic.Co2Schreier
