module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC11_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC11_T1v.F.bin" 12 6 18446744073709551615 3696 13361379075321880595
#kc_repo #kc_blocked_root CFSG.KBData.SchurC11_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC11_T1v.D.bin" 12 4 65535 298 5810853954806042423
#kc_repo #kc_items_root CFSG.KBData.SchurC11_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC11_T1v.Wd.items" 638 7089230594253568693
#kc_repo #kc_items_root CFSG.KBData.SchurC11_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC11_T1v.Wd2.items" 1063 15826552087205381067
#kc_repo #kc_items_root CFSG.KBData.SchurC11_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC11_T1v.R.items" 314 15070928952700369708
#kc_repo #kc_items_root CFSG.KBData.SchurC11_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC11_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC11_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC11_T1v.cv0.items" 1 190 2880253499957178968
#kc_repo #kc_list_root CFSG.KBData.SchurC11_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC11_T1v.wl0.items" 1 3860 15148050803508324859

namespace CFSG.KBRoute.SchurC11

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true true false true false

end CFSG.KBRoute.SchurC11

#kb_table CFSG.KBRoute.SchurC11 T1 SchurC11_T1v include_bytes "data/SchurC11_T1v.meta" 210 10793615205940499488 197121 CFSG.KBRoute.SchurC11.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC11

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC11

#kb_checks SchurC11_T1v include_bytes "data/SchurC11_T1v.meta" 210 10793615205940499488 0

end
