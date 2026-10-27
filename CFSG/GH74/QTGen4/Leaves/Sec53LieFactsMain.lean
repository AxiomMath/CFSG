module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsLieAll

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13

theorem lieFactsAt_G2_leaf
    : Sec53F.LieFactsAt .G2 0 :=
  Sec53F.lieFactsAt_g2

theorem lieFactsAt_D4_leaf
    : Sec53F.LieFactsAt .trialityD4 0 :=
  Sec53F.lieFactsAt_d4

theorem lieFactsAt_F4_leaf
    : Sec53F.LieFactsAt .twistedF4 0 :=
  Sec53F.lieFactsAt_f4

theorem lieFactsAt_U4_leaf : Sec53F.LieFactsAt .PSU 4 :=
  Sec53F.lieFactsAt_u4

theorem lieFactsAt_U5_leaf : Sec53F.LieFactsAt .PSU 5 :=
  Sec53F.lieFactsAt_u5

end CFSG.GH74.QTGen4.Leaves
