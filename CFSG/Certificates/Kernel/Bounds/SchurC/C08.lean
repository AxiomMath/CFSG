module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC08_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC08_T1v.F.bin" 12 6 18446744073709551615 2520 12547980573519088978
#kc_repo #kc_blocked_root CFSG.KBData.SchurC08_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC08_T1v.D.bin" 12 4 65535 218 2398209652087245771
#kc_repo #kc_items_root CFSG.KBData.SchurC08_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC08_T1v.Wd.items" 592 2620620970154001343
#kc_repo #kc_items_root CFSG.KBData.SchurC08_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC08_T1v.Wd2.items" 998 16883223305509573068
#kc_repo #kc_items_root CFSG.KBData.SchurC08_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC08_T1v.R.items" 308 6917690561662990845
#kc_repo #kc_items_root CFSG.KBData.SchurC08_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC08_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC08_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC08_T1v.cv0.items" 1 190 978006732594261631
#kc_repo #kc_list_root CFSG.KBData.SchurC08_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC08_T1v.wl0.items" 1 2628 14990436674791447764

namespace CFSG.KBRoute.SchurC08

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false false false true false

end CFSG.KBRoute.SchurC08

#kb_table CFSG.KBRoute.SchurC08 T1 SchurC08_T1v include_bytes "data/SchurC08_T1v.meta" 195 16687830394478373011 197121 CFSG.KBRoute.SchurC08.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC08

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC08

#kb_checks SchurC08_T1v include_bytes "data/SchurC08_T1v.meta" 195 16687830394478373011 0

end
