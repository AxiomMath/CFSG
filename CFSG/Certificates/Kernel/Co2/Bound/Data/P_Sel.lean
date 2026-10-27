module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Co2.Bound.Data.P_0
public import CFSG.Certificates.Kernel.Co2.Bound.Rels

#kc_repo #kc_nat_items_gz CFSG.KD.Co2BP "CFSG/Certificates/Kernel/Co2/Bound/Data/data/Co2_bound_P_lces_const.items.gz" 76107 17518227572614774790
  WT[1750] RT[10] ST[7] HS nLive
#kc_selectT CFSG.KD.Co2BP blk B 1133
#kc_selectT CFSG.KD.Co2BP selWT WT 1750
#kc_selectT CFSG.KD.Co2BP LVs LV 31
#kc_select CFSG.KD.Co2BP litRT RT 10
#kc_select CFSG.KD.Co2BP litST ST 7

public section

namespace CFSG.KD.Co2BP

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.Co2B.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.Co2B.sub j

end CFSG.KD.Co2BP

end
