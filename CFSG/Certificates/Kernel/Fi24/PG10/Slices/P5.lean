module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P5_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.PG10P5.JF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P5/tab/W_0.bin" 49427 6662907617270748391
#kc_repo #kc_items_root CFSG.KD.PG10P5.loF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P5/tab/W_lo.bin" 14 1367886387021807303
#kc_repo #kc_items_root CFSG.KD.PG10P5.accF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P5/tab/W_acc.bin" 29 12701063431873712005
#kc_repo #kc_items_root CFSG.KD.PG10P5.JV "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P5/tab/C_0.bin" 27718 11257502014907967065
#kc_repo #kc_items_root CFSG.KD.PG10P5.loC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P5/tab/C_lo.bin" 9 13251870035617922631
#kc_repo #kc_items_root CFSG.KD.PG10P5.accC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P5/tab/C_acc.bin" 11 11016669918793620644

namespace CFSG.KD.PG10P5

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 12)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 3456) (nat_lit 12)) JV loC accC i

theorem okW_all : ∀ t < 2, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.PG10P5

end
