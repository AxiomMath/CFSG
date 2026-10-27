module

public import Certificates.Certificate15070

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcU6

theorem census_chain_check :
    censusChainCheck = true :=
  Certificates.certificate15070.1

theorem census_cover_check :
    censusCoverCheck = true :=
  Certificates.certificate15070.2.1

theorem census_size_check :
    censusSizeCheck = true :=
  Certificates.certificate15070.2.2.1

theorem census_point_check :
    censusPointCheck = true :=
  Certificates.certificate15070.2.2.2.1

theorem census_deriv_check :
    censusDerivCheck = true :=
  Certificates.certificate15070.2.2.2.2

end CFSG.ComponentClassification.RankTwoClassical.ExcU6
