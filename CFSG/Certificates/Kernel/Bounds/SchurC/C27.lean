module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC27_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC27_T1v.F.bin" 12 6 18446744073709551615 3376 10389660089075918622
#kc_repo #kc_blocked_root CFSG.KBData.SchurC27_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC27_T1v.D.bin" 12 4 65535 256 12051043454496945176
#kc_repo #kc_items_root CFSG.KBData.SchurC27_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC27_T1v.Wd.items" 694 12660559236271366509
#kc_repo #kc_items_root CFSG.KBData.SchurC27_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC27_T1v.Wd2.items" 1172 15069155694530456586
#kc_repo #kc_items_root CFSG.KBData.SchurC27_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC27_T1v.R.items" 315 1500904771595579621
#kc_repo #kc_items_root CFSG.KBData.SchurC27_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC27_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC27_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC27_T1v.cv0.items" 1 190 10519663128382435662
#kc_repo #kc_list_root CFSG.KBData.SchurC27_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC27_T1v.wl0.items" 1 3715 14681725547332247812

namespace CFSG.KBRoute.SchurC27

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true true false true true

end CFSG.KBRoute.SchurC27

#kb_table CFSG.KBRoute.SchurC27 T1 SchurC27_T1v include_bytes "data/SchurC27_T1v.meta" 207 1677669615413545472 197121 CFSG.KBRoute.SchurC27.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC27

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC27

#kb_checks SchurC27_T1v include_bytes "data/SchurC27_T1v.meta" 207 1677669615413545472 0

end
