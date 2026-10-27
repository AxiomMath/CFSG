module

import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Ru.Bound.Data.C_0
public import CFSG.Certificates.Kernel.Ru.Bound.Lab

#kc_repo #kc_nat_items_gz CFSG.KD.RuBC "CFSG/Certificates/Kernel/Ru/Bound/Data/data/C/lces_const.items.gz" 17104 12739043927303225449
  WT[358] RT[12] ST[2] HS
#kc_selectT CFSG.KD.RuBC blk B 1
#kc_selectT CFSG.KD.RuBC selWT WT 358
#kc_selectT CFSG.KD.RuBC LVs LV 1
#kc_select CFSG.KD.RuBC litRT RT 12
#kc_select CFSG.KD.RuBC litST ST 2
#kc_repo #kc_nat_items_gz CFSG.KD.RuBC "CFSG/Certificates/Kernel/Ru/Bound/Data/data/C/lab_const.items.gz" 1352 4053305316545351932
  L[64]
#kc_select CFSG.KD.RuBC LB L 64

public section

namespace CFSG.KD.RuBC

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.RuB.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.RuB.sub j

end CFSG.KD.RuBC

end
