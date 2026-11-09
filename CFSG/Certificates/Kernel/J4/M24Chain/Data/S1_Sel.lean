module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItems
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.J4.M24Chain.Data.S1_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind

#kc_repo #kc_nat_items CFSG.KD.M24S1 "CFSG/Certificates/Kernel/J4/M24Chain/Data/S1/lces_const.items" 4396 17800178577413339774
  WT[268] RT[11] ST[1] HS
#kc_selectT CFSG.KD.M24S1 blk B 1841
#kc_selectT CFSG.KD.M24S1 selWT WT 268
#kc_selectT CFSG.KD.M24S1 LVs LV 30
#kc_select CFSG.KD.M24S1 litRT RT 11
#kc_select CFSG.KD.M24S1 litST ST 1

public section

namespace CFSG.KD.M24S1

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.M24S1

end
