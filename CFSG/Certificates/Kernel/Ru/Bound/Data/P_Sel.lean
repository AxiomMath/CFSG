module

import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Ru.Bound.Data.P_0
public import CFSG.Certificates.Kernel.Ru.Bound.Lab

#kc_repo #kc_nat_items_gz CFSG.KD.RuBP "CFSG/Certificates/Kernel/Ru/Bound/Data/data/P/lces_const.items.gz" 16945 14903723759525996091
  WT[352] RT[12] ST[2] HS nLive
#kc_selectT CFSG.KD.RuBP blk B 340
#kc_selectT CFSG.KD.RuBP selWT WT 352
#kc_selectT CFSG.KD.RuBP LVs LV 7
#kc_select CFSG.KD.RuBP litRT RT 12
#kc_select CFSG.KD.RuBP litST ST 2

public section

namespace CFSG.KD.RuBP

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.RuB.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.RuB.sub j

end CFSG.KD.RuBP

end
