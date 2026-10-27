module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17613 "c17613.plan.txt" 1815 13515000276261684875
#kc_plan CFSG.KD.M5B.c17613 "c17613.grp.txt" 1200 11346198057429241503
#kc_select CFSG.KD.M5B.c17613 CH CH 54
#kc_select CFSG.KD.M5B.c17613 PRf PR 51
#kc_select CFSG.KD.M5B.c17613 GKf GK 54
#kc_listDispatch CFSG.KD.M5B.c17613 Gf G 6

namespace CFSG.KD.M5B.c17613

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [12, 15] CH PRf Gf g

end CFSG.KD.M5B.c17613

#kc_each CFSG.KD.M5B.c17613.u 0 6

end
