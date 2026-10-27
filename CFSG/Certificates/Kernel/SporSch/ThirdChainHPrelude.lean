module

public import CFSG.Certificates.Kernel.SporSch.ThirdChainHBase

public import CFSG.Assembly.Defs
public import CFSG.Certificates.SubgroupEnumeration
public import Certificates.Data.CFSGNative.Schreier.SetOrbit

@[expose] public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

variable (h : ThirdFactsH)
include h

end CFSG.Sporadic.Co2Schreier
