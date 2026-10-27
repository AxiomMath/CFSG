module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC23_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC23_T1v.F.bin" 12 6 18446744073709551615 3304 1591898163463048296
#kc_repo #kc_blocked_root CFSG.KBData.SchurC23_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC23_T1v.D.bin" 12 4 65535 256 14370366065515117572
#kc_repo #kc_items_root CFSG.KBData.SchurC23_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC23_T1v.Wd.items" 678 4735497423696735075
#kc_repo #kc_items_root CFSG.KBData.SchurC23_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC23_T1v.Wd2.items" 1138 12677999566296239425
#kc_repo #kc_items_root CFSG.KBData.SchurC23_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC23_T1v.R.items" 315 2570302869115904064
#kc_repo #kc_items_root CFSG.KBData.SchurC23_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC23_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC23_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC23_T1v.cv0.items" 1 190 2798274988296429553
#kc_repo #kc_list_root CFSG.KBData.SchurC23_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC23_T1v.wl0.items" 1 3598 1695987100695958379

namespace CFSG.KBRoute.SchurC23

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true true true false true

end CFSG.KBRoute.SchurC23

#kb_table CFSG.KBRoute.SchurC23 T1 SchurC23_T1v include_bytes "data/SchurC23_T1v.meta" 205 14246026651668598743 197121 CFSG.KBRoute.SchurC23.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC23

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC23

#kb_checks SchurC23_T1v include_bytes "data/SchurC23_T1v.meta" 205 14246026651668598743 0

end
