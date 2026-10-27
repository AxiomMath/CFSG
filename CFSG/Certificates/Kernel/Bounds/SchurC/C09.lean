module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC09_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC09_T1v.F.bin" 12 6 18446744073709551615 3488 2122101039515244017
#kc_repo #kc_blocked_root CFSG.KBData.SchurC09_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC09_T1v.D.bin" 12 4 65535 282 15052188566477665434
#kc_repo #kc_items_root CFSG.KBData.SchurC09_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC09_T1v.Wd.items" 637 12110651620822305490
#kc_repo #kc_items_root CFSG.KBData.SchurC09_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC09_T1v.Wd2.items" 1061 2730242271391035022
#kc_repo #kc_items_root CFSG.KBData.SchurC09_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC09_T1v.R.items" 313 2371142558359033030
#kc_repo #kc_items_root CFSG.KBData.SchurC09_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC09_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC09_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC09_T1v.cv0.items" 1 190 13904610827269223817
#kc_repo #kc_list_root CFSG.KBData.SchurC09_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC09_T1v.wl0.items" 1 3654 10481820963732171910

namespace CFSG.KBRoute.SchurC09

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels true false false true false

end CFSG.KBRoute.SchurC09

#kb_table CFSG.KBRoute.SchurC09 T1 SchurC09_T1v include_bytes "data/SchurC09_T1v.meta" 207 8710244829451689788 197121 CFSG.KBRoute.SchurC09.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC09

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC09

#kb_checks SchurC09_T1v include_bytes "data/SchurC09_T1v.meta" 207 8710244829451689788 0

end
