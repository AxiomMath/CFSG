module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.X1_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.M

#kc_repo #kc_nat_items_gz CFSG.KD.Co2KX1 "CFSG/Certificates/Kernel/Co2/Bound3/Data/data/Co2_kill_X1_lces_const.items.gz" 655 14057108533228495637
  WT[36] RT[7] HS
#kc_selectT CFSG.KD.Co2KX1 blk B 5
#kc_selectT CFSG.KD.Co2KX1 selWT WT 36
#kc_selectT CFSG.KD.Co2KX1 LVs LV 1
#kc_select CFSG.KD.Co2KX1 litRT RT 7


public section

namespace CFSG.KD.Co2KX1

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (_j : Nat) : Nat := nat_lit 0

end CFSG.KD.Co2KX1

end
