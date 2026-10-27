module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC24_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC24_T1v.F.bin" 12 6 18446744073709551615 2592 14389769052735910705
#kc_repo #kc_blocked_root CFSG.KBData.SchurC24_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC24_T1v.D.bin" 12 4 65535 220 4329665168316013232
#kc_repo #kc_items_root CFSG.KBData.SchurC24_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC24_T1v.Wd.items" 615 13971955855496020298
#kc_repo #kc_items_root CFSG.KBData.SchurC24_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC24_T1v.Wd2.items" 1030 12107750343410274100
#kc_repo #kc_items_root CFSG.KBData.SchurC24_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC24_T1v.R.items" 309 6922262372393749744
#kc_repo #kc_items_root CFSG.KBData.SchurC24_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC24_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC24_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC24_T1v.cv0.items" 1 190 6097896516009538385
#kc_repo #kc_list_root CFSG.KBData.SchurC24_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC24_T1v.wl0.items" 1 2720 4959263814806827718

namespace CFSG.KBRoute.SchurC24

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false false false true true

end CFSG.KBRoute.SchurC24

#kb_table CFSG.KBRoute.SchurC24 T1 SchurC24_T1v include_bytes "data/SchurC24_T1v.meta" 196 18240023985324221843 197121 CFSG.KBRoute.SchurC24.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC24

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC24

#kb_checks SchurC24_T1v include_bytes "data/SchurC24_T1v.meta" 196 18240023985324221843 0

end
