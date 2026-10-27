module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi24.Data.F2_Sel
public import CFSG.Certificates.Kernel.Fi24.Tab.F2W0
public import CFSG.Certificates.Kernel.Fi24.Tab.F2W1
public import CFSG.Certificates.Kernel.Fi24.Tab.F2W2
public import CFSG.Certificates.Kernel.Fi24.Tab.F2W3
public import CFSG.Certificates.Kernel.Fi24.Tab.F2W4
public import CFSG.Certificates.Kernel.Fi24.Tab.F2C0
public import CFSG.Certificates.Kernel.Fi24.Tab.F2C1
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.TabCat

public section

#kc_tab_cat CFSG.KD.F2.JF CFSG.KD.F2.JFp 5 16
#kc_tab_cat CFSG.KD.F2.JV CFSG.KD.F2.JVp 2 14
#kc_repo #kc_items_root CFSG.KD.F2.loF "CFSG/Certificates/Kernel/Fi24/Tab/data/F2/tab/W_lo.bin" 40250 2073106878660067110
#kc_repo #kc_items_root CFSG.KD.F2.accF "CFSG/Certificates/Kernel/Fi24/Tab/data/F2/tab/W_acc.bin" 64825 15882380361202921159
#kc_repo #kc_items_root CFSG.KD.F2.loC "CFSG/Certificates/Kernel/Fi24/Tab/data/F2/tab/C_lo.bin" 14197 3814486474134443802
#kc_repo #kc_items_root CFSG.KD.F2.accC "CFSG/Certificates/Kernel/Fi24/Tab/data/F2/tab/C_acc.bin" 16501 16528764099631396200

namespace CFSG.KD.F2

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 20)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 9838242) (nat_lit 20)) JV loC accC i

end CFSG.KD.F2

end
