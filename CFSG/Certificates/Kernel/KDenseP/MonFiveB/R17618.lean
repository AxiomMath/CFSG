module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17618 "c17618.plan.txt" 1290 7105136595004803
#kc_plan CFSG.KD.M5B.c17618 "c17618.grp.txt" 864 11918542799425406748
#kc_select CFSG.KD.M5B.c17618 CH CH 39
#kc_select CFSG.KD.M5B.c17618 PRf PR 39
#kc_select CFSG.KD.M5B.c17618 GKf GK 39
#kc_listDispatch CFSG.KD.M5B.c17618 Gf G 3

namespace CFSG.KD.M5B.c17618

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [21] CH PRf Gf g

end CFSG.KD.M5B.c17618

#kc_each CFSG.KD.M5B.c17618.u 0 3

end
