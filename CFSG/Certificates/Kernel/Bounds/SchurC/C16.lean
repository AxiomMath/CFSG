module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC16_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC16_T1v.F.bin" 12 6 18446744073709551615 2528 2716306559100949341
#kc_repo #kc_blocked_root CFSG.KBData.SchurC16_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC16_T1v.D.bin" 12 4 65535 216 7953049781018739788
#kc_repo #kc_items_root CFSG.KBData.SchurC16_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC16_T1v.Wd.items" 657 3628194958411590967
#kc_repo #kc_items_root CFSG.KBData.SchurC16_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC16_T1v.Wd2.items" 1121 14905209344809076350
#kc_repo #kc_items_root CFSG.KBData.SchurC16_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC16_T1v.R.items" 308 18029969308412007895
#kc_repo #kc_items_root CFSG.KBData.SchurC16_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC16_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC16_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC16_T1v.cv0.items" 1 190 2265550880148904931
#kc_repo #kc_list_root CFSG.KBData.SchurC16_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC16_T1v.wl0.items" 1 2721 16175632394561592743

namespace CFSG.KBRoute.SchurC16

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false false false false true

end CFSG.KBRoute.SchurC16

#kb_table CFSG.KBRoute.SchurC16 T1 SchurC16_T1v include_bytes "data/SchurC16_T1v.meta" 196 9053540800641231273 197121 CFSG.KBRoute.SchurC16.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC16

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC16

#kb_checks SchurC16_T1v include_bytes "data/SchurC16_T1v.meta" 196 9053540800641231273 0

end
