module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC15_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC15_T1v.F.bin" 12 6 18446744073709551615 3296 751146418426357802
#kc_repo #kc_blocked_root CFSG.KBData.SchurC15_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC15_T1v.D.bin" 12 4 65535 256 14370366065515117572
#kc_repo #kc_items_root CFSG.KBData.SchurC15_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC15_T1v.Wd.items" 679 14202807226470388269
#kc_repo #kc_items_root CFSG.KBData.SchurC15_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC15_T1v.Wd2.items" 1140 9165249480108720741
#kc_repo #kc_items_root CFSG.KBData.SchurC15_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC15_T1v.R.items" 315 3776010000986094516
#kc_repo #kc_items_root CFSG.KBData.SchurC15_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC15_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC15_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC15_T1v.cv0.items" 1 190 3811158510132619626
#kc_repo #kc_list_root CFSG.KBData.SchurC15_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC15_T1v.wl0.items" 1 3588 5603476142468774336

namespace CFSG.KBRoute.SchurC15

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true true true true false

end CFSG.KBRoute.SchurC15

#kb_table CFSG.KBRoute.SchurC15 T1 SchurC15_T1v include_bytes "data/SchurC15_T1v.meta" 205 2398286823181210131 197121 CFSG.KBRoute.SchurC15.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC15

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC15

#kb_checks SchurC15_T1v include_bytes "data/SchurC15_T1v.meta" 205 2398286823181210131 0

end
