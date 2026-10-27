module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSp44J2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Cert
public import Certificates.Certificate15067

public section

namespace CFSG.ComponentClassification.RankTwoClassical.J2Std

theorem j2A4_check :
    CFSG.ComponentClassification.RankTwoClassical.J2Std.j2A4Check = true :=
  Certificates.certificate15067

theorem j2A4Facts :
    J2A4Facts :=
  j2A4Facts_of_check j2_stdCheck j2A4_check

end CFSG.ComponentClassification.RankTwoClassical.J2Std
