module

public import Certificates.Certificate15001

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.McL

theorem mcl_check :
    mclCheckW mclSG mclRoots mclNodes mclCS mclWCS = true :=
  Certificates.certificate15001

end CFSG.ComponentClassification.RankTwoSporadic.McL
