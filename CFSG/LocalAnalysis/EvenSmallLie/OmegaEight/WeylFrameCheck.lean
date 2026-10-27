module

public import Certificates.Certificate3188

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

theorem equiv_check : equivCheck = true :=
  Certificates.certificate3188.1

theorem frame_check : frameCheck = true :=
  Certificates.certificate3188.2.1

theorem singer_check : singerCheck = true :=
  Certificates.certificate3188.2.2

end CFSG.EvenSmallLie.OmegaEight.Weyl
