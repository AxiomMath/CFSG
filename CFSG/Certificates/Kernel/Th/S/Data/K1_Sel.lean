module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Th.S.Data.K1_0
public import CFSG.Certificates.Kernel.Th.S.TcS
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.LceS

#kc_repo #kc_nat_items_gz CFSG.KD.ThK1 "CFSG/Certificates/Kernel/Th/S/Data/data/K1_Sel.items.gz"
    4480 16217241697567568304
    (WT 0 201) (RT 0 14) HS nLive
#kc_selectT CFSG.KD.ThK1 blk B 304
#kc_selectT CFSG.KD.ThK1 selWT WT 201
#kc_selectT CFSG.KD.ThK1 LVs LV 5
#kc_select CFSG.KD.ThK1 litRT RT 14

public section

namespace CFSG.KD.ThK1

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.Th.TcS.relK (nat_lit 14) r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.Th.TcS.subK (nat_lit 0) j

end CFSG.KD.ThK1

end
