module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC18_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC18_T1v.F.bin" 12 6 18446744073709551615 2536 1332632979157471533
#kc_repo #kc_blocked_root CFSG.KBData.SchurC18_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC18_T1v.D.bin" 12 4 65535 216 7953049781018739788
#kc_repo #kc_items_root CFSG.KBData.SchurC18_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC18_T1v.Wd.items" 669 12137288040678764223
#kc_repo #kc_items_root CFSG.KBData.SchurC18_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC18_T1v.Wd2.items" 1138 4181707053314648048
#kc_repo #kc_items_root CFSG.KBData.SchurC18_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC18_T1v.R.items" 309 3476192002268295711
#kc_repo #kc_items_root CFSG.KBData.SchurC18_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC18_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC18_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC18_T1v.cv0.items" 1 190 14732471067146364656
#kc_repo #kc_list_root CFSG.KBData.SchurC18_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC18_T1v.wl0.items" 1 2734 3347438512247209974

namespace CFSG.KBRoute.SchurC18

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false true false false true

end CFSG.KBRoute.SchurC18

#kb_table CFSG.KBRoute.SchurC18 T1 SchurC18_T1v include_bytes "data/SchurC18_T1v.meta" 196 18058191311463042610 197121 CFSG.KBRoute.SchurC18.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC18

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC18

#kb_checks SchurC18_T1v include_bytes "data/SchurC18_T1v.meta" 196 18058191311463042610 0

end
