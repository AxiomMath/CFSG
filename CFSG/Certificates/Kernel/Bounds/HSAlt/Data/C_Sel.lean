module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Data.C_0
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Rels
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Lab
public import CFSG.Certificates.Kernel.Bounds.HSAlt.Model

#kc_repo #kc_nat_items_gz CFSG.KD.HSKC "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/C/lces_const.items.gz" 48313 16093826958742460129
  WT[1095] RT[13] ST[30] HS
#kc_selectT CFSG.KD.HSKC blk B 15
#kc_selectT CFSG.KD.HSKC selWT WT 1095
#kc_selectT CFSG.KD.HSKC LVs LV 1
#kc_select CFSG.KD.HSKC litRT RT 13
#kc_select CFSG.KD.HSKC litST ST 30
#kc_repo #kc_nat_items_gz CFSG.KD.HSKC "CFSG/Certificates/Kernel/Bounds/HSAlt/Data/C/lab_const.items.gz" 473 15048948510839319614
  LBITS

public section

namespace CFSG.KD.HSKC

@[expose] noncomputable def selRT (r : Nat) : Nat := CFSG.KC.HSK.rel r

@[expose] noncomputable def selST (j : Nat) : Nat := CFSG.KC.HSK.subS j

@[expose] noncomputable def LB (i : Nat) : Nat := Nat.land (Nat.shiftRight LBITS i) (nat_lit 1)

@[expose] noncomputable def LETs (j : Nat) : Nat := CFSG.KC.HSK.psiGen j

end CFSG.KD.HSKC

end
