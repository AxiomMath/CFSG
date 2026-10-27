module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X2_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M

#kc_repo #kc_nat_items_gz CFSG.KD.Fi22KX2 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X2/lces_const.items.gz" 1592 11177482857167855213
  WT[92] RT[18] ST[4] HS
#kc_selectT CFSG.KD.Fi22KX2 blk B 79
#kc_selectT CFSG.KD.Fi22KX2 selWT WT 92
#kc_selectT CFSG.KD.Fi22KX2 LVs LV 1
#kc_select CFSG.KD.Fi22KX2 litRT RT 18
#kc_select CFSG.KD.Fi22KX2 litST ST 4

public section

namespace CFSG.KD.Fi22KX2

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.Fi22KX2

end
