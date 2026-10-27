module

public import Certificates.Certificate3222

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

theorem unique_check : uniqueCheck = true :=
  Certificates.certificate3222.1

theorem centerC_check : centerCCheck = true :=
  Certificates.certificate3222.2.1

theorem centerMod_check : centerModCheck = true :=
  Certificates.certificate3222.2.2.1

theorem commSet_check : commSetCheck = true :=
  Certificates.certificate3222.2.2.2

end CFSG.EvenSmallLie.OmegaEight.Weyl
