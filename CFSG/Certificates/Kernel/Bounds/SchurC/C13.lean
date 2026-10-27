module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC13_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC13_T1v.F.bin" 12 6 18446744073709551615 3296 751146418426357802
#kc_repo #kc_blocked_root CFSG.KBData.SchurC13_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC13_T1v.D.bin" 12 4 65535 256 14370366065515117572
#kc_repo #kc_items_root CFSG.KBData.SchurC13_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC13_T1v.Wd.items" 678 5447200203132403558
#kc_repo #kc_items_root CFSG.KBData.SchurC13_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC13_T1v.Wd2.items" 1138 10463516643411501005
#kc_repo #kc_items_root CFSG.KBData.SchurC13_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC13_T1v.R.items" 314 16218030674141513136
#kc_repo #kc_items_root CFSG.KBData.SchurC13_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC13_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC13_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC13_T1v.cv0.items" 1 190 3811158510132619626
#kc_repo #kc_list_root CFSG.KBData.SchurC13_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC13_T1v.wl0.items" 1 3586 5929708135853702587

namespace CFSG.KBRoute.SchurC13

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true false true true false

end CFSG.KBRoute.SchurC13

#kb_table CFSG.KBRoute.SchurC13 T1 SchurC13_T1v include_bytes "data/SchurC13_T1v.meta" 205 6925483450387300752 197121 CFSG.KBRoute.SchurC13.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC13

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC13

#kb_checks SchurC13_T1v include_bytes "data/SchurC13_T1v.meta" 205 6925483450387300752 0

end
