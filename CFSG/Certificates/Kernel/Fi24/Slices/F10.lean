module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.Data.F10_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.F10.JF "CFSG/Certificates/Kernel/Fi24/Slices/data/F10/tab/W_0.bin" 56 6053586130931527617
#kc_repo #kc_items_root CFSG.KD.F10.loF "CFSG/Certificates/Kernel/Fi24/Slices/data/F10/tab/W_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F10.accF "CFSG/Certificates/Kernel/Fi24/Slices/data/F10/tab/W_acc.bin" 18 14031217384261203422
#kc_repo #kc_items_root CFSG.KD.F10.JV "CFSG/Certificates/Kernel/Fi24/Slices/data/F10/tab/C_0.bin" 51 11060395708993031021
#kc_repo #kc_items_root CFSG.KD.F10.loC "CFSG/Certificates/Kernel/Fi24/Slices/data/F10/tab/C_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F10.accC "CFSG/Certificates/Kernel/Fi24/Slices/data/F10/tab/C_acc.bin" 10 6827484803816487544

namespace CFSG.KD.F10

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 4)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 6) (nat_lit 4)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.F10

end
