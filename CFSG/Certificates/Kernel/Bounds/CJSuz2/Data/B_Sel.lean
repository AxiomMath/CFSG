module

import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Bounds.CJSuz2.Data.B_0
public import CFSG.Certificates.Kernel.Common.LabF
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo


#kc_repo #kc_nat_items_gz CFSG.KD.CJSuz2B "CFSG/Certificates/Kernel/Bounds/CJSuz2/B/data/lces_const.items.gz" 583 7372561757889502766
    (WT 0 5) (RT 0 4) ST0 HS nLive
#kc_select CFSG.KD.CJSuz2B blk B 1
#kc_select CFSG.KD.CJSuz2B selWT WT 5
#kc_select CFSG.KD.CJSuz2B LVs LV 1
#kc_select CFSG.KD.CJSuz2B litRT RT 4
#kc_select CFSG.KD.CJSuz2B litST ST 1

public section

namespace CFSG.KD.CJSuz2B

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.CJSuz2B

end
