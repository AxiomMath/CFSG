module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.B_0
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.B_1
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.B_2
public import CFSG.Certificates.Kernel.Common.LabF


#kc_repo #kc_nat_items_gz CFSG.KD.J3AB "CFSG/Certificates/Kernel/Bounds/J3Alt/Data/B/lces_const.items.gz" 74381 3416454944845140162
  WT[434] RT[30] ST0 HS nLive
#kc_select CFSG.KD.J3AB blk B 134
#kc_select CFSG.KD.J3AB selWT WT 434
#kc_select CFSG.KD.J3AB LVs LV 4
#kc_select CFSG.KD.J3AB litRT RT 30
#kc_select CFSG.KD.J3AB litST ST 1

public section

namespace CFSG.KD.J3AB

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.J3AB

end
