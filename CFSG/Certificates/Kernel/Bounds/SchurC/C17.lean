module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC17_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC17_T1v.F.bin" 12 6 18446744073709551615 3400 4843507407714966235
#kc_repo #kc_blocked_root CFSG.KBData.SchurC17_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC17_T1v.D.bin" 12 4 65535 258 3276393394561769010
#kc_repo #kc_items_root CFSG.KBData.SchurC17_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC17_T1v.Wd.items" 626 12298502355849602017
#kc_repo #kc_items_root CFSG.KBData.SchurC17_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC17_T1v.Wd2.items" 1043 7741887601163049976
#kc_repo #kc_items_root CFSG.KBData.SchurC17_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC17_T1v.R.items" 313 6370353770983431322
#kc_repo #kc_items_root CFSG.KBData.SchurC17_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC17_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC17_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC17_T1v.cv0.items" 1 190 3649803241832489135
#kc_repo #kc_list_root CFSG.KBData.SchurC17_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC17_T1v.wl0.items" 1 3658 16801496690637907340

namespace CFSG.KBRoute.SchurC17

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true false false false true

end CFSG.KBRoute.SchurC17

#kb_table CFSG.KBRoute.SchurC17 T1 SchurC17_T1v include_bytes "data/SchurC17_T1v.meta" 207 11847878920143431266 197121 CFSG.KBRoute.SchurC17.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC17

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC17

#kb_checks SchurC17_T1v include_bytes "data/SchurC17_T1v.meta" 207 11847878920143431266 0

end
