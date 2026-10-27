module

import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_0
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_1
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_2
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_3
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_4
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_5
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_6
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_7
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_8
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_9
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_10
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_11
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_12
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_13
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_14
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_15
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_16
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_17
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_18
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_19
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_20
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_21
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_22
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_23
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_24
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_25
public import CFSG.Certificates.Kernel.Common.LabF

#kc_repo #kc_nat_items_gz CFSG.KD.RuBAB "CFSG/Certificates/Kernel/Ru/BoundAlt/Data/data/B/lces_const.items.gz" 289086 5965873215584435533
  WT[6749] RT[81] ST[2] HS nLive
#kc_selectT CFSG.KD.RuBAB blk B 1624
#kc_selectT CFSG.KD.RuBAB selWT WT 6749
#kc_selectT CFSG.KD.RuBAB LVs LV 35
#kc_select CFSG.KD.RuBAB litRT RT 81
#kc_select CFSG.KD.RuBAB litST ST 2

public section

namespace CFSG.KD.RuBAB

@[expose] noncomputable def selRT (r : Nat) : Nat := litRT r

@[expose] noncomputable def selST (j : Nat) : Nat := litST j

end CFSG.KD.RuBAB

end
