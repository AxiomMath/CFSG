module

public import Certificates.Certificate15044
public import Certificates.Certificate15045
public import Certificates.Certificate15046

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

theorem co1_cen2ACheck : co1Cen2ACheck co1Cen2AGlobal co1Cen2AS1
    co1Cen2AS2 co1Cen2AD1 co1Cen2AD2 co1Cen2AZH1
    co1Cen2AZH2 co1Cen2ADec1 co1Cen2ADec2 co1Cen2AQD co1Cen2AQE = true :=
  Certificates.certificate15044

theorem co1_cen2BCheck : co1Cen2BCheck co1Cen2BH co1Cen2BUV
    co1Cen2BC co1Cen2BIC = true :=
  Certificates.certificate15045

theorem co1_cen2CCheck : co1Cen2CCheck co1Cen2CGlobal co1Cen2CS1
    co1Cen2CS2 co1Cen2CD1 co1Cen2CD2 co1Cen2CZH1
    co1Cen2CZH2 co1Cen2CDec1 co1Cen2CDec2 co1Cen2CRD co1Cen2CRE = true :=
  Certificates.certificate15046

end CFSG.ComponentClassification.RankTwoSporadic.Co1
