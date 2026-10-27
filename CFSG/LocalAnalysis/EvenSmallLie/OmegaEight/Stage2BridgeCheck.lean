module

public import Certificates.Certificate3412

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

theorem bridge_check_plus :
    ∃ cE tcE sE : Enum, enumOK cGensPlus cE = true ∧ enumOK tGensPlus tcE = true ∧
      bridgeCheck .plus cGensPlus tGensPlus cE tcE sE = true :=
  Certificates.certificate3412.1

theorem bridge_check_minus :
    ∃ cE tcE sE : Enum, enumOK cGensMinus cE = true ∧ enumOK tGensMinus tcE = true ∧
      bridgeCheck .minus cGensMinus tGensMinus cE tcE sE = true :=
  Certificates.certificate3412.2

end CFSG.EvenSmallLie.OmegaEight.Stage2
