module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Th.S.Data.K3_0
public import CFSG.Certificates.Kernel.Th.S.TcS
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.LceS

#kc_repo #kc_nat_items_gz CFSG.KD.ThK3 "CFSG/Certificates/Kernel/Th/S/Data/data/K3_Sel.items.gz"
    6537 12911268038261432035
    (WT 0 342) (RT 0 27) (ST 0 5) HS nLive
#kc_selectT CFSG.KD.ThK3 blk B 2156
#kc_selectT CFSG.KD.ThK3 selWT WT 342
#kc_selectT CFSG.KD.ThK3 LVs LV 27
#kc_select CFSG.KD.ThK3 litRT RT 27

public section

namespace CFSG.KD.ThK3

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.Th.TcS.relK (nat_lit 27) r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.Th.TcS.subK (nat_lit 5) j

end CFSG.KD.ThK3

end
