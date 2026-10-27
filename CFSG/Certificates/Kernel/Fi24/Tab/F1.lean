module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi24.Data.F1_Sel
public import CFSG.Certificates.Kernel.Fi24.Tab.F1W0
public import CFSG.Certificates.Kernel.Fi24.Tab.F1W1
public import CFSG.Certificates.Kernel.Fi24.Tab.F1W2
public import CFSG.Certificates.Kernel.Fi24.Tab.F1W3
public import CFSG.Certificates.Kernel.Fi24.Tab.F1C0
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.TabCat

public section

#kc_tab_cat CFSG.KD.F1.JF CFSG.KD.F1.JFp 4 16
#kc_repo #kc_items_root CFSG.KD.F1.loF "CFSG/Certificates/Kernel/Fi24/Tab/data/F1/tab/W_lo.bin" 27840 16102055216673153080
#kc_repo #kc_items_root CFSG.KD.F1.accF "CFSG/Certificates/Kernel/Fi24/Tab/data/F1/tab/W_acc.bin" 45221 13279776970688820846
#kc_repo #kc_items_root CFSG.KD.F1.loC "CFSG/Certificates/Kernel/Fi24/Tab/data/F1/tab/C_lo.bin" 7088 960558014625715664
#kc_repo #kc_items_root CFSG.KD.F1.accC "CFSG/Certificates/Kernel/Fi24/Tab/data/F1/tab/C_acc.bin" 8199 15324571513559399076

namespace CFSG.KD.F1

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 24)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 6653548) (nat_lit 24)) JV loC accC i

end CFSG.KD.F1

end
