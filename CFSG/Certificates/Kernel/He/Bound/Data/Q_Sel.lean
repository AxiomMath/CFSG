module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.He.Bound.Data.Q_0
public import CFSG.Certificates.Kernel.He.Bound.Lab

#kc_repo #kc_nat_items_gz CFSG.KD.HeBQ "CFSG/Certificates/Kernel/He/Bound/Data/data/Q/lces_const.items.gz" 137947 12280621031689285160
  WT[375] RT[6] ST0 HS nLive
#kc_selectT CFSG.KD.HeBQ blk B 183
#kc_selectT CFSG.KD.HeBQ selWT WT 375
#kc_selectT CFSG.KD.HeBQ LVs LV 6
#kc_select CFSG.KD.HeBQ litRT RT 6
#kc_select CFSG.KD.HeBQ litST ST 1

public section

namespace CFSG.KD.HeBQ

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.HeBQ

end
