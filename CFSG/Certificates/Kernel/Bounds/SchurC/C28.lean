module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC28_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC28_T1v.F.bin" 12 6 18446744073709551615 2424 4425090399476856883
#kc_repo #kc_blocked_root CFSG.KBData.SchurC28_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC28_T1v.D.bin" 12 4 65535 214 3459321228842040275
#kc_repo #kc_items_root CFSG.KBData.SchurC28_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC28_T1v.Wd.items" 645 12919685561181074046
#kc_repo #kc_items_root CFSG.KBData.SchurC28_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC28_T1v.Wd2.items" 1095 9281167141362452256
#kc_repo #kc_items_root CFSG.KBData.SchurC28_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC28_T1v.R.items" 310 8482672131929058388
#kc_repo #kc_items_root CFSG.KBData.SchurC28_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC28_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC28_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC28_T1v.cv0.items" 1 190 9566019081562231648
#kc_repo #kc_list_root CFSG.KBData.SchurC28_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC28_T1v.wl0.items" 1 2570 4407500893006938266

namespace CFSG.KBRoute.SchurC28

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false false true true true

end CFSG.KBRoute.SchurC28

#kb_table CFSG.KBRoute.SchurC28 T1 SchurC28_T1v include_bytes "data/SchurC28_T1v.meta" 195 3761067931068487005 197121 CFSG.KBRoute.SchurC28.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC28

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC28

#kb_checks SchurC28_T1v include_bytes "data/SchurC28_T1v.meta" 195 3761067931068487005 0

end
