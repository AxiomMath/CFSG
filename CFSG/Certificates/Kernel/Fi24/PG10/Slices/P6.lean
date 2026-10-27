module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P6_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.PG10P6.JF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P6/tab/W_0.bin" 166109 15367987604476463344
#kc_repo #kc_items_root CFSG.KD.PG10P6.loF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P6/tab/W_lo.bin" 37 7678626969800391850
#kc_repo #kc_items_root CFSG.KD.PG10P6.accF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P6/tab/W_acc.bin" 69 5629288931691797303
#kc_repo #kc_items_root CFSG.KD.PG10P6.JV "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P6/tab/C_0.bin" 101114 14806773636104865818
#kc_repo #kc_items_root CFSG.KD.PG10P6.loC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P6/tab/C_lo.bin" 24 4595120249344820591
#kc_repo #kc_items_root CFSG.KD.PG10P6.accC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P6/tab/C_acc.bin" 29 15432962342805070889

namespace CFSG.KD.PG10P6

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 10)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 12600) (nat_lit 10)) JV loC accC i

theorem okW_all : ∀ t < 6, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 4, okC t = true := by
  kc_cover 1

end CFSG.KD.PG10P6

end
