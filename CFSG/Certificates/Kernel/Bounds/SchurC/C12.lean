module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC12_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC12_T1v.F.bin" 12 6 18446744073709551615 2352 15733013346312632930
#kc_repo #kc_blocked_root CFSG.KBData.SchurC12_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC12_T1v.D.bin" 12 4 65535 212 9956899451774723267
#kc_repo #kc_items_root CFSG.KBData.SchurC12_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC12_T1v.Wd.items" 622 1270571875765437853
#kc_repo #kc_items_root CFSG.KBData.SchurC12_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC12_T1v.Wd2.items" 1063 11845932079507432298
#kc_repo #kc_items_root CFSG.KBData.SchurC12_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC12_T1v.R.items" 309 6424305649468540890
#kc_repo #kc_items_root CFSG.KBData.SchurC12_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC12_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC12_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC12_T1v.cv0.items" 1 190 8014154190808996387
#kc_repo #kc_list_root CFSG.KBData.SchurC12_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC12_T1v.wl0.items" 1 2474 7942532757875423133

namespace CFSG.KBRoute.SchurC12

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false false true true false

end CFSG.KBRoute.SchurC12

#kb_table CFSG.KBRoute.SchurC12 T1 SchurC12_T1v include_bytes "data/SchurC12_T1v.meta" 192 17305682550794303632 197121 CFSG.KBRoute.SchurC12.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC12

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC12

#kb_checks SchurC12_T1v include_bytes "data/SchurC12_T1v.meta" 192 17305682550794303632 0

end
