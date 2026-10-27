module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC20_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC20_T1v.F.bin" 12 6 18446744073709551615 2440 10981257689857314876
#kc_repo #kc_blocked_root CFSG.KBData.SchurC20_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC20_T1v.D.bin" 12 4 65535 214 3459321228842040275
#kc_repo #kc_items_root CFSG.KBData.SchurC20_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC20_T1v.Wd.items" 642 10511547686678466644
#kc_repo #kc_items_root CFSG.KBData.SchurC20_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC20_T1v.Wd2.items" 1091 10632696700275762517
#kc_repo #kc_items_root CFSG.KBData.SchurC20_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC20_T1v.R.items" 309 2361696082272118111
#kc_repo #kc_items_root CFSG.KBData.SchurC20_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC20_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC20_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC20_T1v.cv0.items" 1 190 3845241048179611993
#kc_repo #kc_list_root CFSG.KBData.SchurC20_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC20_T1v.wl0.items" 1 2589 7364256977797169812

namespace CFSG.KBRoute.SchurC20

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false false true false true

end CFSG.KBRoute.SchurC20

#kb_table CFSG.KBRoute.SchurC20 T1 SchurC20_T1v include_bytes "data/SchurC20_T1v.meta" 195 12928423634841234066 197121 CFSG.KBRoute.SchurC20.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC20

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC20

#kb_checks SchurC20_T1v include_bytes "data/SchurC20_T1v.meta" 195 12928423634841234066 0

end
