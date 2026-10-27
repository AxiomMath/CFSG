module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelNative
public import Certificates.Certificate10021
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelNative
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

namespace CFSG.ComponentClassification.J2Cover.Kernel

theorem cpACheck_eq : cpACheck = true :=
  Certificates.certificate10021.1

theorem crACheck_eq : crACheck = true :=
  Certificates.certificate10021.2.1

theorem cpTCheck_eq : cpTCheck = true :=
  Certificates.certificate10021.2.2.1

theorem crTCheck_eq : crTCheck = true :=
  Certificates.certificate10021.2.2.2.1

theorem crUCheck_eq : crUCheck = true :=
  Certificates.certificate10021.2.2.2.2

end CFSG.ComponentClassification.J2Cover.Kernel
