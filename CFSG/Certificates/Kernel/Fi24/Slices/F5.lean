module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.Data.F5_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.F5.JF "CFSG/Certificates/Kernel/Fi24/Slices/data/F5/tab/W_0.bin" 9245 14439519878521768500
#kc_repo #kc_items_root CFSG.KD.F5.loF "CFSG/Certificates/Kernel/Fi24/Slices/data/F5/tab/W_lo.bin" 9 17768578827557278944
#kc_repo #kc_items_root CFSG.KD.F5.accF "CFSG/Certificates/Kernel/Fi24/Slices/data/F5/tab/W_acc.bin" 18 3576970314277852670
#kc_repo #kc_items_root CFSG.KD.F5.JV "CFSG/Certificates/Kernel/Fi24/Slices/data/F5/tab/C_0.bin" 3144 279085966061422376
#kc_repo #kc_items_root CFSG.KD.F5.loC "CFSG/Certificates/Kernel/Fi24/Slices/data/F5/tab/C_lo.bin" 9 13717715311587276296
#kc_repo #kc_items_root CFSG.KD.F5.accC "CFSG/Certificates/Kernel/Fi24/Slices/data/F5/tab/C_acc.bin" 10 1569200524452011885

namespace CFSG.KD.F5

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 14)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 392) (nat_lit 14)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.F5

end
