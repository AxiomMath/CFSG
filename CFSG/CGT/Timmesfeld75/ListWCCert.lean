module

public import CFSG.CGT.Timmesfeld75.ListWCMathieu
public import Certificates.Certificate21102

public section

namespace CFSG.CGT.Timmesfeld75

theorem m22WCCheck_holds : M22WCCheck :=
  Certificates.certificate21102.1

theorem m23WCCheck_holds : M23WCCheck :=
  Certificates.certificate21102.2.1

theorem m24WCCheck_holds : M24WCCheck :=
  Certificates.certificate21102.2.2

theorem listWCIdentification_of_cert :
    ListWCIdentification :=
  listWCIdentification m22WCCheck_holds m23WCCheck_holds m24WCCheck_holds

end CFSG.CGT.Timmesfeld75
