module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalNative
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalNative
public import Certificates.Certificate4151
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

namespace CFSG.QuasithinUnique.Id2519.Tab

open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover (autStrong autBase chainTables)
open CFSG.ComponentClassification.J2Cover.External (tblX tblY)

set_option compiler.extract_closed false

theorem centPD_check :
    countProducts 315 (commAll 315 [tblX, tblY]) (chainTables 315 autStrong autBase) (idT 315) =
      1 :=
  Certificates.certificate4151

end CFSG.QuasithinUnique.Id2519.Tab
