module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC05_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC05_T1v.F.bin" 12 6 18446744073709551615 3296 751146418426357802
#kc_repo #kc_blocked_root CFSG.KBData.SchurC05_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC05_T1v.D.bin" 12 4 65535 256 14370366065515117572
#kc_repo #kc_items_root CFSG.KBData.SchurC05_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC05_T1v.Wd.items" 676 9185811490261666540
#kc_repo #kc_items_root CFSG.KBData.SchurC05_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC05_T1v.Wd2.items" 1134 2889861956763088932
#kc_repo #kc_items_root CFSG.KBData.SchurC05_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC05_T1v.R.items" 313 3784900250888088923
#kc_repo #kc_items_root CFSG.KBData.SchurC05_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC05_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC05_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC05_T1v.cv0.items" 1 190 3811158510132619626
#kc_repo #kc_list_root CFSG.KBData.SchurC05_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC05_T1v.wl0.items" 1 3583 16107470010192920232

namespace CFSG.KBRoute.SchurC05

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true false true false false

end CFSG.KBRoute.SchurC05

#kb_table CFSG.KBRoute.SchurC05 T1 SchurC05_T1v include_bytes "data/SchurC05_T1v.meta" 205 16421238795180060780 197121 CFSG.KBRoute.SchurC05.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC05

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC05

#kb_checks SchurC05_T1v include_bytes "data/SchurC05_T1v.meta" 205 16421238795180060780 0

end
