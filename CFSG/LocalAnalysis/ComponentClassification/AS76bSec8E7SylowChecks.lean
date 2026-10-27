module

public import Certificates.Certificate15093

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.SeitzReduction


theorem e7SylowCheck_y : e7SylowCheck oddDerivE7YFrame e7SylowCertY = true :=
  Certificates.certificate15093.1

theorem e7SylowCheck_z : e7SylowCheck oddDerivE7ZFrame e7SylowCertZ = true :=
  Certificates.certificate15093.2.1

theorem e7SylowCheck_u : e7SylowCheck oddDerivE7UFrame e7SylowCertU = true :=
  Certificates.certificate15093.2.2.1

theorem e7SylowCheck_v : e7SylowCheck oddDerivE7VFrame e7SylowCertV = true :=
  Certificates.certificate15093.2.2.2

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
