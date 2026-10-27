module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC06_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC06_T1v.F.bin" 12 6 18446744073709551615 2432 4638903205900364127
#kc_repo #kc_blocked_root CFSG.KBData.SchurC06_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC06_T1v.D.bin" 12 4 65535 214 3459321228842040275
#kc_repo #kc_items_root CFSG.KBData.SchurC06_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC06_T1v.Wd.items" 653 16113135317786939128
#kc_repo #kc_items_root CFSG.KBData.SchurC06_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC06_T1v.Wd2.items" 1106 10635529852438107829
#kc_repo #kc_items_root CFSG.KBData.SchurC06_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC06_T1v.R.items" 309 385579575130653769
#kc_repo #kc_items_root CFSG.KBData.SchurC06_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC06_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC06_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC06_T1v.cv0.items" 1 190 2885270887389910231
#kc_repo #kc_list_root CFSG.KBData.SchurC06_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC06_T1v.wl0.items" 1 2577 2693797359269860913

namespace CFSG.KBRoute.SchurC06

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false true true false false

end CFSG.KBRoute.SchurC06

#kb_table CFSG.KBRoute.SchurC06 T1 SchurC06_T1v include_bytes "data/SchurC06_T1v.meta" 195 9311975588686615822 197121 CFSG.KBRoute.SchurC06.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC06

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC06

#kb_checks SchurC06_T1v include_bytes "data/SchurC06_T1v.meta" 195 9311975588686615822 0

end
