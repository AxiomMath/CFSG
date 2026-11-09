module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItems
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.J4.M24Chain.Data.S2_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind

#kc_repo #kc_nat_items CFSG.KD.M24S2 "CFSG/Certificates/Kernel/J4/M24Chain/Data/S2/lces_const.items" 1852 2712355412644483489
  WT[102] RT[29] ST[4] HS
#kc_selectT CFSG.KD.M24S2 blk B 1
#kc_selectT CFSG.KD.M24S2 selWT WT 102
#kc_selectT CFSG.KD.M24S2 LVs LV 1
#kc_select CFSG.KD.M24S2 litRT RT 29
#kc_select CFSG.KD.M24S2 litST ST 4

public section

namespace CFSG.KD.M24S2

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.M24S2

end
