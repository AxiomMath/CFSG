module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.X2_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.M

#kc_repo #kc_nat_items_gz CFSG.KD.HSKX2 "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/X2/lces_const.items.gz" 5999 5507770389751145131
  WT[185] RT[60] ST[2] HS
#kc_selectT CFSG.KD.HSKX2 blk B 16
#kc_selectT CFSG.KD.HSKX2 selWT WT 185
#kc_selectT CFSG.KD.HSKX2 LVs LV 1
#kc_select CFSG.KD.HSKX2 litRT RT 60
#kc_select CFSG.KD.HSKX2 litST ST 2


public section

namespace CFSG.KD.HSKX2

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.HSKX2

end
