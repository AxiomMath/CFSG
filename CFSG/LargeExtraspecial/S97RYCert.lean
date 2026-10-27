module

public import CFSG.LargeExtraspecial.S97RYMain
public import Certificates.Certificate21103

public section

namespace CFSG.LargeExtraspecial.S11

theorem a9PairCheck_holds : A9PairCheck :=
  Certificates.certificate21103.1

theorem m22PairCheck_holds : M22PairCheck :=
  Certificates.certificate21103.2

theorem a9WCPairFact : A9WCPairFact :=
  a9WCPairFact_of a9PairCheck_holds

theorem m22WCPairFact :
    M22WCPairFact :=
  m22WCPairFact_of m22PairCheck_holds

end CFSG.LargeExtraspecial.S11
