module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P3_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.PG10P3.JF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P3/tab/W_0.bin" 18520 6371315243499590418
#kc_repo #kc_items_root CFSG.KD.PG10P3.loF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P3/tab/W_lo.bin" 9 86152377345325695
#kc_repo #kc_items_root CFSG.KD.PG10P3.accF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P3/tab/W_acc.bin" 18 9988750961873009100
#kc_repo #kc_items_root CFSG.KD.PG10P3.JV "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P3/tab/C_0.bin" 7695 7809416171577221644
#kc_repo #kc_items_root CFSG.KD.PG10P3.loC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P3/tab/C_lo.bin" 9 8169068019159600108
#kc_repo #kc_items_root CFSG.KD.PG10P3.accC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P3/tab/C_acc.bin" 10 18326302239456929291

namespace CFSG.KD.PG10P3

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 16)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 960) (nat_lit 16)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.PG10P3

end
