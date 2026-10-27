module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC10_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC10_T1v.F.bin" 12 6 18446744073709551615 2584 6445239039580416589
#kc_repo #kc_blocked_root CFSG.KBData.SchurC10_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC10_T1v.D.bin" 12 4 65535 220 4329665168316013232
#kc_repo #kc_items_root CFSG.KBData.SchurC10_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC10_T1v.Wd.items" 626 12091786362635978569
#kc_repo #kc_items_root CFSG.KBData.SchurC10_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC10_T1v.Wd2.items" 1045 11051319228202841796
#kc_repo #kc_items_root CFSG.KBData.SchurC10_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC10_T1v.R.items" 309 13607491096515623405
#kc_repo #kc_items_root CFSG.KBData.SchurC10_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC10_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC10_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC10_T1v.cv0.items" 1 190 9423548938796182799
#kc_repo #kc_list_root CFSG.KBData.SchurC10_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC10_T1v.wl0.items" 1 2709 9091608517905235320

namespace CFSG.KBRoute.SchurC10

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false true false true false

end CFSG.KBRoute.SchurC10

#kb_table CFSG.KBRoute.SchurC10 T1 SchurC10_T1v include_bytes "data/SchurC10_T1v.meta" 196 6622129107593347374 197121 CFSG.KBRoute.SchurC10.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC10

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC10

#kb_checks SchurC10_T1v include_bytes "data/SchurC10_T1v.meta" 196 6622129107593347374 0

end
