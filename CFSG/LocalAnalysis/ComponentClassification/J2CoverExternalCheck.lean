module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalNative
public import Certificates.Certificate10020
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalNative
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

namespace CFSG.ComponentClassification.J2Cover.External

theorem chainCheck_eq : chainCheck = true :=
  Certificates.certificate10020.1

theorem tableCheck_eq : tableCheck = true :=
  Certificates.certificate10020.2.1

theorem elemCheck_eq : elemCheck = true :=
  Certificates.certificate10020.2.2.1

theorem lamCheck_eq : lamCheck = true :=
  Certificates.certificate10020.2.2.2

end CFSG.ComponentClassification.J2Cover.External
