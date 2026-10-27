module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.Data.F11_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.F11.JF "CFSG/Certificates/Kernel/Fi24/Slices/data/F11/tab/W_0.bin" 10 9206340999432161901
#kc_repo #kc_items_root CFSG.KD.F11.loF "CFSG/Certificates/Kernel/Fi24/Slices/data/F11/tab/W_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F11.accF "CFSG/Certificates/Kernel/Fi24/Slices/data/F11/tab/W_acc.bin" 18 8159119712174035969
#kc_repo #kc_items_root CFSG.KD.F11.JV "CFSG/Certificates/Kernel/Fi24/Slices/data/F11/tab/C_0.bin" 19 13556311258996104984
#kc_repo #kc_items_root CFSG.KD.F11.loC "CFSG/Certificates/Kernel/Fi24/Slices/data/F11/tab/C_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F11.accC "CFSG/Certificates/Kernel/Fi24/Slices/data/F11/tab/C_acc.bin" 10 8671675252724093981

namespace CFSG.KD.F11

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 2)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 2) (nat_lit 2)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.F11

end
