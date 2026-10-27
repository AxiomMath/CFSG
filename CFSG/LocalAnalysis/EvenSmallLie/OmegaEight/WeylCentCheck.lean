module

public import Certificates.Certificate3220

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

theorem dFix_check : dFixCheck = true :=
  Certificates.certificate3220.1

theorem sOrbit_check : sOrbitCheck = true :=
  Certificates.certificate3220.2.1

theorem frameRefl_check : frameReflCheck = true :=
  Certificates.certificate3220.2.2.1

theorem wt2Fix_check : wt2FixCheck = true :=
  Certificates.certificate3220.2.2.2.1

theorem triple_check : tripleCheck = true :=
  Certificates.certificate3220.2.2.2.2.1

theorem pair2_check : pairCheck2 = true :=
  Certificates.certificate3220.2.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.Weyl
