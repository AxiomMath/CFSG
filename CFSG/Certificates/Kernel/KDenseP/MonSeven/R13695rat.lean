module

public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M7.c13695rat

open CFSG.KC.KDenseP.MonSeven

@[expose] noncomputable def P : Prs := tri e13695rat []

end CFSG.KD.M7.c13695rat

#kc_plan CFSG.KD.M7.c13695rat "c13695rat.plan.txt" 1605 9708558594072890463
#kc_plan CFSG.KD.M7.c13695rat "c13695rat.grp.txt" 788 16929265911801427440
#kc_select CFSG.KD.M7.c13695rat CH CH 36
#kc_select CFSG.KD.M7.c13695rat IXf IX 36
#kc_select CFSG.KD.M7.c13695rat PRf PR 33
#kc_select CFSG.KD.M7.c13695rat GKf GK 36
#kc_listDispatch CFSG.KD.M7.c13695rat Gf G 6

namespace CFSG.KD.M7.c13695rat

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M7L.grpRP P CH PRf Gf g

end CFSG.KD.M7.c13695rat

#kc_each CFSG.KD.M7.c13695rat.u 0 6

end
