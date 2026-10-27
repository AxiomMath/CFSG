module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC02_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC02_T1v.F.bin" 12 6 18446744073709551615 2744 11421383245669416638
#kc_repo #kc_blocked_root CFSG.KBData.SchurC02_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC02_T1v.D.bin" 12 4 65535 234 4926131526520285034
#kc_repo #kc_items_root CFSG.KBData.SchurC02_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC02_T1v.Wd.items" 570 1248289145648971214
#kc_repo #kc_items_root CFSG.KBData.SchurC02_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC02_T1v.Wd2.items" 968 8541651255755511463
#kc_repo #kc_items_root CFSG.KBData.SchurC02_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC02_T1v.R.items" 308 8918852841739961678
#kc_repo #kc_items_root CFSG.KBData.SchurC02_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC02_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC02_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC02_T1v.cv0.items" 1 190 6938154868616823845
#kc_repo #kc_list_root CFSG.KBData.SchurC02_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC02_T1v.wl0.items" 1 2854 733676329400719589

namespace CFSG.KBRoute.SchurC02

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false true false false false

end CFSG.KBRoute.SchurC02

#kb_table CFSG.KBRoute.SchurC02 T1 SchurC02_T1v include_bytes "data/SchurC02_T1v.meta" 199 4765563150300652041 197121 CFSG.KBRoute.SchurC02.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC02

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC02

#kb_checks SchurC02_T1v include_bytes "data/SchurC02_T1v.meta" 199 4765563150300652041 0

end
