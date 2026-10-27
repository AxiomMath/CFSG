module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC22_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC22_T1v.F.bin" 12 6 18446744073709551615 2448 16287801645928490212
#kc_repo #kc_blocked_root CFSG.KBData.SchurC22_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC22_T1v.D.bin" 12 4 65535 214 3459321228842040275
#kc_repo #kc_items_root CFSG.KBData.SchurC22_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC22_T1v.Wd.items" 654 13085949857348527536
#kc_repo #kc_items_root CFSG.KBData.SchurC22_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC22_T1v.Wd2.items" 1108 4023354097557705480
#kc_repo #kc_items_root CFSG.KBData.SchurC22_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC22_T1v.R.items" 310 7079429265932280957
#kc_repo #kc_items_root CFSG.KBData.SchurC22_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC22_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC22_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC22_T1v.cv0.items" 1 190 17386808860173814315
#kc_repo #kc_list_root CFSG.KBData.SchurC22_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC22_T1v.wl0.items" 1 2601 14940186187796373525

namespace CFSG.KBRoute.SchurC22

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false true true false true

end CFSG.KBRoute.SchurC22

#kb_table CFSG.KBRoute.SchurC22 T1 SchurC22_T1v include_bytes "data/SchurC22_T1v.meta" 195 9293481430121990147 197121 CFSG.KBRoute.SchurC22.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC22

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC22

#kb_checks SchurC22_T1v include_bytes "data/SchurC22_T1v.meta" 195 9293481430121990147 0

end
