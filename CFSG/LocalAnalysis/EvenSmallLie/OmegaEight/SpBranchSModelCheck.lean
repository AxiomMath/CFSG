module

public import Certificates.Certificate3870

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem sRange_check : sRangeCheck = true :=
  Certificates.certificate3870.1

theorem sAssoc_check : sAssocCheck = true :=
  Certificates.certificate3870.2.1

theorem sUnit_check : sUnitCheck = true :=
  Certificates.certificate3870.2.2.1

theorem sAct_check : sActCheck = true :=
  Certificates.certificate3870.2.2.2

end CFSG.EvenSmallLie.OmegaEight.SpBranch
