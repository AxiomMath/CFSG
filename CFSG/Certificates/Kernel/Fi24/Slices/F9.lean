module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.Data.F9_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.F9.JF "CFSG/Certificates/Kernel/Fi24/Slices/data/F9/tab/W_0.bin" 138 10634492178597413376
#kc_repo #kc_items_root CFSG.KD.F9.loF "CFSG/Certificates/Kernel/Fi24/Slices/data/F9/tab/W_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F9.accF "CFSG/Certificates/Kernel/Fi24/Slices/data/F9/tab/W_acc.bin" 18 166856172126223472
#kc_repo #kc_items_root CFSG.KD.F9.JV "CFSG/Certificates/Kernel/Fi24/Slices/data/F9/tab/C_0.bin" 99 17915766608945540087
#kc_repo #kc_items_root CFSG.KD.F9.loC "CFSG/Certificates/Kernel/Fi24/Slices/data/F9/tab/C_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.F9.accC "CFSG/Certificates/Kernel/Fi24/Slices/data/F9/tab/C_acc.bin" 10 16492258418245317181

namespace CFSG.KD.F9

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 6)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 12) (nat_lit 6)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.F9

end
