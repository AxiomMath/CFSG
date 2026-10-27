module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X1_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M

#kc_repo #kc_nat_items_gz CFSG.KD.Fi22KX1 "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X1/lces_const.items.gz" 632 12782944278414518399
  WT[30] RT[13] HS
#kc_selectT CFSG.KD.Fi22KX1 blk B 108
#kc_selectT CFSG.KD.Fi22KX1 selWT WT 30
#kc_selectT CFSG.KD.Fi22KX1 LVs LV 2
#kc_select CFSG.KD.Fi22KX1 litRT RT 13


public section

namespace CFSG.KD.Fi22KX1

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (_j : Nat) : Nat := nat_lit 0

end CFSG.KD.Fi22KX1

end
