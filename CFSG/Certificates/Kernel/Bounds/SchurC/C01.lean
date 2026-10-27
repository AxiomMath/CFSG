module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC01_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC01_T1v.F.bin" 12 6 18446744073709551615 3392 2297241581625055056
#kc_repo #kc_blocked_root CFSG.KBData.SchurC01_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC01_T1v.D.bin" 12 4 65535 258 3276393394561769010
#kc_repo #kc_items_root CFSG.KBData.SchurC01_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC01_T1v.Wd.items" 625 15193906609291140655
#kc_repo #kc_items_root CFSG.KBData.SchurC01_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC01_T1v.Wd2.items" 1041 11092821820671181306
#kc_repo #kc_items_root CFSG.KBData.SchurC01_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC01_T1v.R.items" 312 17597601357607732360
#kc_repo #kc_items_root CFSG.KBData.SchurC01_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC01_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC01_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC01_T1v.cv0.items" 1 190 1081104242637872269
#kc_repo #kc_list_root CFSG.KBData.SchurC01_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC01_T1v.wl0.items" 1 3646 11854111595782116855

namespace CFSG.KBRoute.SchurC01

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true false false false false

end CFSG.KBRoute.SchurC01

#kb_table CFSG.KBRoute.SchurC01 T1 SchurC01_T1v include_bytes "data/SchurC01_T1v.meta" 207 1728620011516187043 197121 CFSG.KBRoute.SchurC01.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC01

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC01

#kb_checks SchurC01_T1v include_bytes "data/SchurC01_T1v.meta" 207 1728620011516187043 0

end
