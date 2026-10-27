module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P4_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.PG10P4.JF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P4/tab/W_0.bin" 264 4503933890889065611
#kc_repo #kc_items_root CFSG.KD.PG10P4.loF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P4/tab/W_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.PG10P4.accF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P4/tab/W_acc.bin" 18 10924456986686117972
#kc_repo #kc_items_root CFSG.KD.PG10P4.JV "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P4/tab/C_0.bin" 59 2500677353998492009
#kc_repo #kc_items_root CFSG.KD.PG10P4.loC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P4/tab/C_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.PG10P4.accC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P4/tab/C_acc.bin" 10 15916976828904412554

namespace CFSG.KD.PG10P4

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 14)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 7) (nat_lit 14)) JV loC accC i

theorem okW_all : ∀ t < 1, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 1, okC t = true := by
  kc_cover 1

end CFSG.KD.PG10P4

end
