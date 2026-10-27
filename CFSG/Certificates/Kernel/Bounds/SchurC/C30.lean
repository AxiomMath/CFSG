module

public import CFSG.Certificates.Kernel.Bounds.Hdr
public import CFSG.Certificates.Kernel.Bounds.Checks
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Bounds.SchurC.Rels
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.Certificates

public section

#kc_repo #kc_blocked_root CFSG.KBData.SchurC30_T1v.F "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC30_T1v.F.bin" 12 6 18446744073709551615 2432 1459255876032488857
#kc_repo #kc_blocked_root CFSG.KBData.SchurC30_T1v.D "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC30_T1v.D.bin" 12 4 65535 214 3459321228842040275
#kc_repo #kc_items_root CFSG.KBData.SchurC30_T1v.Wd "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC30_T1v.Wd.items" 657 2639604292658688675
#kc_repo #kc_items_root CFSG.KBData.SchurC30_T1v.Wd2 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC30_T1v.Wd2.items" 1112 3842622217878038680
#kc_repo #kc_items_root CFSG.KBData.SchurC30_T1v.R "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC30_T1v.R.items" 311 13685596276444783729
#kc_repo #kc_items_root CFSG.KBData.SchurC30_T1v.S "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC30_T1v.S.items" 133 17848464801915827291
#kc_repo #kc_list_root CFSG.KBData.SchurC30_T1v.cv0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC30_T1v.cv0.items" 1 190 1977798158971943251
#kc_repo #kc_list_root CFSG.KBData.SchurC30_T1v.wl0 "CFSG/Certificates/Kernel/Bounds/SchurC/data/SchurC30_T1v.wl0.items" 1 2583 6077693847215572224

namespace CFSG.KBRoute.SchurC30

@[expose] def rels : List (List (Nat × Bool)) := CFSG.KC.SchurC.crels false true true true true

end CFSG.KBRoute.SchurC30

#kb_table CFSG.KBRoute.SchurC30 T1 SchurC30_T1v include_bytes "data/SchurC30_T1v.meta" 195 11162426803975929935 197121 CFSG.KBRoute.SchurC30.rels "1,2,1,1,2,1,1,2,1,1,2,1 1,-2,1,1,-2,1,1,-2,1,1,-2,1 2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2,2,1,2,1,-2 2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2,2,1,-2,1,-2 -2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2,-2,1,-2,1,2,1,2,1,2"

namespace CFSG.KBRoute.SchurC30

theorem top : KB.topOk T1.amap (nat_lit 3) = true := by quickRfl

end CFSG.KBRoute.SchurC30

#kb_checks SchurC30_T1v include_bytes "data/SchurC30_T1v.meta" 195 11162426803975929935 0

end
