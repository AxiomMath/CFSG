module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.He.Bound.Data.P_0
public import CFSG.Certificates.Kernel.He.Bound.Data.P_1
public import CFSG.Certificates.Kernel.He.Bound.Data.P_2
public import CFSG.Certificates.Kernel.He.Bound.Data.P_3
public import CFSG.Certificates.Kernel.He.Bound.Lab

#kc_repo #kc_nat_items_gz CFSG.KD.HeBP "CFSG/Certificates/Kernel/He/Bound/Data/data/P/lces_const.items.gz" 64439 15746352885985690292
  WT[1698] RT[7] ST[2] HS nLive
#kc_selectT CFSG.KD.HeBP blk B 4523
#kc_selectT CFSG.KD.HeBP selWT WT 1698
#kc_selectT CFSG.KD.HeBP LVs LV 139
#kc_select CFSG.KD.HeBP litRT RT 7
#kc_select CFSG.KD.HeBP litST ST 2

public section

namespace CFSG.KD.HeBP

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.HeB.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.HeB.sub j

end CFSG.KD.HeBP

end
