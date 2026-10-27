module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X3_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M

#kc_repo #kc_nat_items_gz CFSG.KD.Fi22KX3 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X3/lces_const.items.gz" 4054 7572705567185271916
  WT[241] RT[23] ST[5] HS
#kc_selectT CFSG.KD.Fi22KX3 blk B 220
#kc_selectT CFSG.KD.Fi22KX3 selWT WT 241
#kc_selectT CFSG.KD.Fi22KX3 LVs LV 3
#kc_select CFSG.KD.Fi22KX3 litRT RT 23
#kc_select CFSG.KD.Fi22KX3 litST ST 5

public section

namespace CFSG.KD.Fi22KX3

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.Fi22KX3

end
