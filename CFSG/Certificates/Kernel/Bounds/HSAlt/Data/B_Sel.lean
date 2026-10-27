module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.B_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Rels
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Lab

#kc_repo #kc_nat_items_gz CFSG.KD.HSKB "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/B/lces_const.items.gz" 20085 17507483601808642019
  WT[463] RT[13] ST[5] HS
#kc_selectT CFSG.KD.HSKB blk B 244
#kc_selectT CFSG.KD.HSKB selWT WT 463
#kc_selectT CFSG.KD.HSKB LVs LV 7
#kc_select CFSG.KD.HSKB litRT RT 13
#kc_select CFSG.KD.HSKB litST ST 5


public section

namespace CFSG.KD.HSKB

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.HSK.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.HSK.subB j

end CFSG.KD.HSKB

end
