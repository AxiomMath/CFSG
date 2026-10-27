module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.Data.F6_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.F6.JF "CFSG/Certificates/Kernel/Fi24/Slices/data/F6/tab/W_0.bin" 2507 9162274125161163682
#kc_repo #kc_items_root CFSG.KD.F6.loF "CFSG/Certificates/Kernel/Fi24/Slices/data/F6/tab/W_lo.bin" 9 8323320492795997591
#kc_repo #kc_items_root CFSG.KD.F6.accF "CFSG/Certificates/Kernel/Fi24/Slices/data/F6/tab/W_acc.bin" 18 4505629102470679728
#kc_repo #kc_items_root CFSG.KD.F6.JV "CFSG/Certificates/Kernel/Fi24/Slices/data/F6/tab/C_0.bin" 1300 1523467966517775509
#kc_repo #kc_items_root CFSG.KD.F6.loC "CFSG/Certificates/Kernel/Fi24/Slices/data/F6/tab/C_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F6.accC "CFSG/Certificates/Kernel/Fi24/Slices/data/F6/tab/C_acc.bin" 10 4899026902068531100

namespace CFSG.KD.F6

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 12)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 162) (nat_lit 12)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.F6

end
