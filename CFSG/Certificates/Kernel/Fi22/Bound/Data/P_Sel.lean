module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.P_0
public import CFSG.Certificates.Kernel.Fi22.Bound.Rels

#kc_repo #kc_nat_items_gz CFSG.KD.Fi22BP "CFSG/Certificates/Kernel/Fi22/Bound/Data/P/lces_const.items.gz" 22364 11627339986107463892
  WT[640] RT[13] ST[7] HS nLive
#kc_selectT CFSG.KD.Fi22BP blk B 323
#kc_selectT CFSG.KD.Fi22BP selWT WT 640
#kc_selectT CFSG.KD.Fi22BP LVs LV 9
#kc_select CFSG.KD.Fi22BP litRT RT 13
#kc_select CFSG.KD.Fi22BP litST ST 7

public section

namespace CFSG.KD.Fi22BP

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.Fi22B.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.Fi22B.sub j

end CFSG.KD.Fi22BP

end
