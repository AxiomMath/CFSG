module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC04_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC04_T1v.F.bin" 12 6 18446744073709551615 2368 5326232957863106396
#kc_repo #kc_blocked_root CFSG.KBData.SchurC04_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC04_T1v.D.bin" 12 4 65535 212 9956899451774723267
#kc_repo #kc_items_root CFSG.KBData.SchurC04_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC04_T1v.Wd.items" 619 9036212002191791935
#kc_repo #kc_items_root CFSG.KBData.SchurC04_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC04_T1v.Wd2.items" 1059 8877727605260543796
#kc_repo #kc_items_root CFSG.KBData.SchurC04_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC04_T1v.R.items" 308 6023524238560011838
#kc_repo #kc_items_root CFSG.KBData.SchurC04_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC04_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC04_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC04_T1v.cv0.items" 1 190 1932320149388829191
#kc_repo #kc_list_root CFSG.KBData.SchurC04_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC04_T1v.wl0.items" 1 2492 12157880155080076149

namespace CFSG.KBRoute.SchurC04

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false false true false false

end CFSG.KBRoute.SchurC04

#kb_table CFSG.KBRoute.SchurC04 T1 SchurC04_T1v include_bytes "data/SchurC04_T1v.meta" 192 6250107486663470524 197121 CFSG.KBRoute.SchurC04.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC04

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC04

#kb_checks SchurC04_T1v include_bytes "data/SchurC04_T1v.meta" 192 6250107486663470524 0

end
