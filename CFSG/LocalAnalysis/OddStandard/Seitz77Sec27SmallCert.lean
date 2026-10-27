module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Small
public import Certificates.Certificate6129
public import Certificates.Certificate6130

public section

namespace CFSG.OddStandard.Seitz77

theorem notU42_of_certificate :
    NotU42 :=
  notU42 Certificates.certificate6129

theorem notJ2_of_certificate :
    NotJ2 :=
  notJ2 Certificates.certificate6130

end CFSG.OddStandard.Seitz77
