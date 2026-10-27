module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.X2_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.M

#kc_repo #kc_nat_items_gz CFSG.KD.Co2KX2 "CFSG/Certificates/Kernel/Co2/Bound3/Data/data/Co2_kill_X2_lces_const.items.gz" 5394 9696695261520765531
  WT[286] RT[13] ST[3] HS
#kc_selectT CFSG.KD.Co2KX2 blk B 319
#kc_selectT CFSG.KD.Co2KX2 selWT WT 286
#kc_selectT CFSG.KD.Co2KX2 LVs LV 6
#kc_select CFSG.KD.Co2KX2 litRT RT 13
#kc_select CFSG.KD.Co2KX2 litST ST 3

public section

namespace CFSG.KD.Co2KX2

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.Co2KX2

end
