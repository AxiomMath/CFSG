module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC31_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC31_T1v.F.bin" 12 6 18446744073709551615 3304 1591898163463048296
#kc_repo #kc_blocked_root CFSG.KBData.SchurC31_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC31_T1v.D.bin" 12 4 65535 256 14370366065515117572
#kc_repo #kc_items_root CFSG.KBData.SchurC31_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC31_T1v.Wd.items" 680 16475864352101559896
#kc_repo #kc_items_root CFSG.KBData.SchurC31_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC31_T1v.Wd2.items" 1142 4976952552619319685
#kc_repo #kc_items_root CFSG.KBData.SchurC31_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC31_T1v.R.items" 316 13039469946235847590
#kc_repo #kc_items_root CFSG.KBData.SchurC31_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC31_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC31_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC31_T1v.cv0.items" 1 190 2798274988296429553
#kc_repo #kc_list_root CFSG.KBData.SchurC31_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC31_T1v.wl0.items" 1 3601 2814486725356539153

namespace CFSG.KBRoute.SchurC31

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true true true true true

end CFSG.KBRoute.SchurC31

#kb_table CFSG.KBRoute.SchurC31 T1 SchurC31_T1v include_bytes "data/SchurC31_T1v.meta" 205 2738742966677166139 197121 CFSG.KBRoute.SchurC31.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC31

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC31

#kb_checks SchurC31_T1v include_bytes "data/SchurC31_T1v.meta" 205 2738742966677166139 0

end
