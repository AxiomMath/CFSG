module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.Data.F4_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.F4.JF "CFSG/Certificates/Kernel/Fi24/Slices/data/F4/tab/W_0.bin" 20814 6930057978206338053
#kc_repo #kc_items_root CFSG.KD.F4.loF "CFSG/Certificates/Kernel/Fi24/Slices/data/F4/tab/W_lo.bin" 9 86152377345325695
#kc_repo #kc_items_root CFSG.KD.F4.accF "CFSG/Certificates/Kernel/Fi24/Slices/data/F4/tab/W_acc.bin" 18 9988750961873009100
#kc_repo #kc_items_root CFSG.KD.F4.JV "CFSG/Certificates/Kernel/Fi24/Slices/data/F4/tab/C_0.bin" 7696 18288550056947733549
#kc_repo #kc_items_root CFSG.KD.F4.loC "CFSG/Certificates/Kernel/Fi24/Slices/data/F4/tab/C_lo.bin" 9 8169068019159600108
#kc_repo #kc_items_root CFSG.KD.F4.accC "CFSG/Certificates/Kernel/Fi24/Slices/data/F4/tab/C_acc.bin" 10 18326302239456929291

namespace CFSG.KD.F4

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 16)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 960) (nat_lit 16)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.F4

end
