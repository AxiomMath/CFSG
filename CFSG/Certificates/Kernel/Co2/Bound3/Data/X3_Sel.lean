module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.X3_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.M

#kc_repo #kc_nat_items_gz CFSG.KD.Co2KX3 "CFSG/Certificates/Kernel/Co2/Bound3/Data/data/Co2_kill_X3_lces_const.items.gz" 6541 9369352144775077148
  WT[332] RT[23] ST[4] HS
#kc_selectT CFSG.KD.Co2KX3 blk B 546
#kc_selectT CFSG.KD.Co2KX3 selWT WT 332
#kc_selectT CFSG.KD.Co2KX3 LVs LV 11
#kc_select CFSG.KD.Co2KX3 litRT RT 23
#kc_select CFSG.KD.Co2KX3 litST ST 4

public section

namespace CFSG.KD.Co2KX3

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.Co2KX3

end
