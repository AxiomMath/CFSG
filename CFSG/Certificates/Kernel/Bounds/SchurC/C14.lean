module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC14_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC14_T1v.F.bin" 12 6 18446744073709551615 2416 3248485228825966847
#kc_repo #kc_blocked_root CFSG.KBData.SchurC14_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC14_T1v.D.bin" 12 4 65535 214 3459321228842040275
#kc_repo #kc_items_root CFSG.KBData.SchurC14_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC14_T1v.Wd.items" 656 3573898076051616973
#kc_repo #kc_items_root CFSG.KBData.SchurC14_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC14_T1v.Wd2.items" 1110 1922498999501015994
#kc_repo #kc_items_root CFSG.KBData.SchurC14_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC14_T1v.R.items" 310 9452420209423183410
#kc_repo #kc_items_root CFSG.KBData.SchurC14_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC14_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC14_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC14_T1v.cv0.items" 1 190 4858598953628161985
#kc_repo #kc_list_root CFSG.KBData.SchurC14_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC14_T1v.wl0.items" 1 2558 4437470203607906237

namespace CFSG.KBRoute.SchurC14

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false true true true false

end CFSG.KBRoute.SchurC14

#kb_table CFSG.KBRoute.SchurC14 T1 SchurC14_T1v include_bytes "data/SchurC14_T1v.meta" 195 3789898280965694180 197121 CFSG.KBRoute.SchurC14.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC14

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC14

#kb_checks SchurC14_T1v include_bytes "data/SchurC14_T1v.meta" 195 3789898280965694180 0

end
