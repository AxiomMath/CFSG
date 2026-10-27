module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.T_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Rels
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Lab

#kc_repo #kc_nat_items_gz CFSG.KD.HSKT "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/T/lces_const.items.gz" 48313 16093826958742460129
  WT[1095] RT[13] ST[30] HS
#kc_selectT CFSG.KD.HSKT blk B 166
#kc_selectT CFSG.KD.HSKT selWT WT 1095
#kc_selectT CFSG.KD.HSKT LVs LV 5
#kc_select CFSG.KD.HSKT litRT RT 13
#kc_select CFSG.KD.HSKT litST ST 30


public section

namespace CFSG.KD.HSKT

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.HSK.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.HSK.subS j

end CFSG.KD.HSKT

end
