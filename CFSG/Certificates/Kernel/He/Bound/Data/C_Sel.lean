module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.He.Bound.Data.C_0
public import CFSG.Certificates.Kernel.He.Bound.Lab

#kc_repo #kc_nat_items_gz CFSG.KD.HeBC "CFSG/Certificates/Kernel/He/Bound/Data/data/C/lces_const.items.gz" 64531 13764733564364474620
  WT[1701] RT[7] ST[2] HS
#kc_selectT CFSG.KD.HeBC blk B 7
#kc_selectT CFSG.KD.HeBC selWT WT 1701
#kc_selectT CFSG.KD.HeBC LVs LV 1
#kc_select CFSG.KD.HeBC litRT RT 7
#kc_select CFSG.KD.HeBC litST ST 2
#kc_repo #kc_nat_items_gz CFSG.KD.HeBC "CFSG/Certificates/Kernel/He/Bound/Data/data/C/lab_const.items.gz" 56906 1932566253721614326
  L[1628]
#kc_select CFSG.KD.HeBC LB L 1628

public section

namespace CFSG.KD.HeBC

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.HeB.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.HeB.sub j

end CFSG.KD.HeBC

end
