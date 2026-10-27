module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public meta import Certificates.Data.CFSGNative.J2.Certificate
public import Certificates.Certificate4067

public section

namespace CFSG.QuasithinUnique.Setup.X1

theorem j2_ta_eq :
    j2Data.ta.toList = CFSG.QuasithinUnique.K1.SporadicPerm.j2ta :=
  Certificates.certificate4067.1

theorem j2_tb_eq :
    j2Data.tb.toList = CFSG.QuasithinUnique.K1.SporadicPerm.j2tb :=
  Certificates.certificate4067.2

end CFSG.QuasithinUnique.Setup.X1
