module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4Cover
public import Certificates.Certificate15042
public import Certificates.Certificate15043

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J4

theorem j4_foxCert :
    CFSG.Sporadic.Recognition.J4Multiplier.J4FoxCert :=
  Certificates.certificate15042

theorem j4_formCert :
    CFSG.Sporadic.Recognition.J4Multiplier.J4FormCert :=
  Certificates.certificate15043

theorem j4NoDoubleCover_checked :
    J4NoDoubleCover :=
  j4NoDoubleCover j4_foxCert j4_formCert

end CFSG.ComponentClassification.RankTwoSporadic.J4
