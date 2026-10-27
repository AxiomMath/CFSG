module

public import Certificates.Certificate3185

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

theorem pair_check : pairCheck = true :=
  Certificates.certificate3185.1

theorem zWord_check : zWordCheck = true :=
  Certificates.certificate3185.2.1

theorem om_check : omCheck = true :=
  Certificates.certificate3185.2.2.1

theorem sZero_check : sZeroCheck = true :=
  Certificates.certificate3185.2.2.2.1

theorem triality_check : trialityCheck = true :=
  Certificates.certificate3185.2.2.2.2

end CFSG.EvenSmallLie.OmegaEight.Weyl
