module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.X1_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.M

#kc_repo #kc_nat_items_gz CFSG.KD.HSKX1 "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/X1/lces_const.items.gz" 723 13161466864647366758
  WT[17] RT[18] HS
#kc_selectT CFSG.KD.HSKX1 blk B 1
#kc_selectT CFSG.KD.HSKX1 selWT WT 17
#kc_selectT CFSG.KD.HSKX1 LVs LV 1
#kc_select CFSG.KD.HSKX1 litRT RT 18



public section

namespace CFSG.KD.HSKX1

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (_j : Nat) : Nat := nat_lit 0

end CFSG.KD.HSKX1

end
