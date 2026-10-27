module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Th.S.Data.K2_0
public import CFSG.Certificates.Kernel.Th.S.TcS
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.LceS

#kc_repo #kc_nat_items_gz CFSG.KD.ThK2 "CFSG/Certificates/Kernel/Th/S/Data/data/K2_Sel.items.gz"
    5717 12048435663163338120
    (WT 0 280) (RT 0 20) (ST 0 5) HS nLive
#kc_selectT CFSG.KD.ThK2 blk B 680
#kc_selectT CFSG.KD.ThK2 selWT WT 280
#kc_selectT CFSG.KD.ThK2 LVs LV 10
#kc_select CFSG.KD.ThK2 litRT RT 20

public section

namespace CFSG.KD.ThK2

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.Th.TcS.relK (nat_lit 20) r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.Th.TcS.subK (nat_lit 5) j

end CFSG.KD.ThK2

end
