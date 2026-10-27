module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.X3_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.M

#kc_repo #kc_nat_items_gz CFSG.KD.HSKX3 "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/X3/lces_const.items.gz" 4248 18199751965339579266
  WT[114] RT[87] ST[3] HS
#kc_selectT CFSG.KD.HSKX3 blk B 1
#kc_selectT CFSG.KD.HSKX3 selWT WT 114
#kc_selectT CFSG.KD.HSKX3 LVs LV 1
#kc_select CFSG.KD.HSKX3 litRT RT 87
#kc_select CFSG.KD.HSKX3 litST ST 3


public section

namespace CFSG.KD.HSKX3

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.HSKX3

end
