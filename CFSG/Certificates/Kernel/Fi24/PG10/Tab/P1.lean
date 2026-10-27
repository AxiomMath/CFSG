module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P1_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Tab.P1W0
public import CFSG.Certificates.Kernel.Fi24.PG10.Tab.P1W1
public import CFSG.Certificates.Kernel.Fi24.PG10.Tab.P1W2
public import CFSG.Certificates.Kernel.Fi24.PG10.Tab.P1W3
public import CFSG.Certificates.Kernel.Fi24.PG10.Tab.P1W4
public import CFSG.Certificates.Kernel.Fi24.PG10.Tab.P1C0
public import CFSG.Certificates.Kernel.Fi24.PG10.Tab.P1C1
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.TabCat

public section

#kc_tab_cat CFSG.KD.PG10P1.JF CFSG.KD.PG10P1.JFp 5 16
#kc_tab_cat CFSG.KD.PG10P1.JV CFSG.KD.PG10P1.JVp 2 14
#kc_repo #kc_items_root CFSG.KD.PG10P1.loF "CFSG/Certificates/Kernel/Fi24/PG10/Tab/data/P1/tab/W_lo.bin" 40694 2216169984859460175
#kc_repo #kc_items_root CFSG.KD.PG10P1.accF "CFSG/Certificates/Kernel/Fi24/PG10/Tab/data/P1/tab/W_acc.bin" 65121 8998439120373753448
#kc_repo #kc_items_root CFSG.KD.PG10P1.loC "CFSG/Certificates/Kernel/Fi24/PG10/Tab/data/P1/tab/C_lo.bin" 12417 3709364496715951028
#kc_repo #kc_items_root CFSG.KD.PG10P1.accC "CFSG/Certificates/Kernel/Fi24/PG10/Tab/data/P1/tab/C_acc.bin" 14346 3437687639049972838

namespace CFSG.KD.PG10P1

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 20)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 8696903) (nat_lit 20)) JV loC accC i

end CFSG.KD.PG10P1

end
