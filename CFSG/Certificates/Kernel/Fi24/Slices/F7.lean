module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.Data.F7_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.F7.JF "CFSG/Certificates/Kernel/Fi24/Slices/data/F7/tab/W_0.bin" 713 6240903866143402075
#kc_repo #kc_items_root CFSG.KD.F7.loF "CFSG/Certificates/Kernel/Fi24/Slices/data/F7/tab/W_lo.bin" 9 13717715311587276296
#kc_repo #kc_items_root CFSG.KD.F7.accF "CFSG/Certificates/Kernel/Fi24/Slices/data/F7/tab/W_acc.bin" 18 5588350789915697507
#kc_repo #kc_items_root CFSG.KD.F7.JV "CFSG/Certificates/Kernel/Fi24/Slices/data/F7/tab/C_0.bin" 403 6914288259662332086
#kc_repo #kc_items_root CFSG.KD.F7.loC "CFSG/Certificates/Kernel/Fi24/Slices/data/F7/tab/C_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F7.accC "CFSG/Certificates/Kernel/Fi24/Slices/data/F7/tab/C_acc.bin" 10 16468404889533139282

namespace CFSG.KD.F7

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 10)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 50) (nat_lit 10)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.F7

end
