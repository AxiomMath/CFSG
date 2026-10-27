module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutModel
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import Certificates.Certificate4105
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover

set_option compiler.extract_closed false

theorem j2_pair_five_total :
    classTotal 315 #[tblA, tblB] #[tblAInv, tblBInv] (orderTablesOf (idT 315) 2)
      (orderTablesOf (idT 315) 5) 4000 5 2 2 5 = 0 :=
  Certificates.certificate4105

end CFSG.QuasithinUnique.A5.G3
