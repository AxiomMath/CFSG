module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.Data.F8_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.F8.JF "CFSG/Certificates/Kernel/Fi24/Slices/data/F8/tab/W_0.bin" 425 14218782166044375160
#kc_repo #kc_items_root CFSG.KD.F8.loF "CFSG/Certificates/Kernel/Fi24/Slices/data/F8/tab/W_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F8.accF "CFSG/Certificates/Kernel/Fi24/Slices/data/F8/tab/W_acc.bin" 18 7235484200282676151
#kc_repo #kc_items_root CFSG.KD.F8.JV "CFSG/Certificates/Kernel/Fi24/Slices/data/F8/tab/C_0.bin" 259 9992360024913562717
#kc_repo #kc_items_root CFSG.KD.F8.loC "CFSG/Certificates/Kernel/Fi24/Slices/data/F8/tab/C_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F8.accC "CFSG/Certificates/Kernel/Fi24/Slices/data/F8/tab/C_acc.bin" 10 18370117418474859984

namespace CFSG.KD.F8

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 8)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 32) (nat_lit 8)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.F8

end
