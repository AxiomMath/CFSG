module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Co2.Bound3.Data.P4_0
public import CFSG.Certificates.Kernel.Co2.Bound.Rels
public import CFSG.Certificates.Kernel.Co2.Bound3.Rels
public import CFSG.Certificates.Kernel.Co2.Bound3.Lab

#kc_repo #kc_nat_items_gz CFSG.KD.Co2KP4 "CFSG/Certificates/Kernel/Co2/Bound3/Data/data/Co2_kill_P4_lces_const.items.gz" 43407 4616894113085836365
  WT[1143] RT[10] ST[4] HS
#kc_selectT CFSG.KD.Co2KP4 blk B 540
#kc_selectT CFSG.KD.Co2KP4 selWT WT 1143
#kc_selectT CFSG.KD.Co2KP4 LVs LV 16
#kc_select CFSG.KD.Co2KP4 litRT RT 10
#kc_select CFSG.KD.Co2KP4 litST ST 4

public section

namespace CFSG.KD.Co2KP4

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.Co2B.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.Co2K.subH j

end CFSG.KD.Co2KP4

end
