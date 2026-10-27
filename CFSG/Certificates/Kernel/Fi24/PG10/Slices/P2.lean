module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P2_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.PG10P2.JF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P2/tab/W_0.bin" 5864811 18350955882155208829
#kc_repo #kc_items_root CFSG.KD.PG10P2.loF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P2/tab/W_lo.bin" 1197 12023854846236446617
#kc_repo #kc_items_root CFSG.KD.PG10P2.accF "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P2/tab/W_acc.bin" 1999 15697324977694600236
#kc_repo #kc_items_root CFSG.KD.PG10P2.JV "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P2/tab/C_0.bin" 2052002 8796806689762452293
#kc_repo #kc_items_root CFSG.KD.PG10P2.loC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P2/tab/C_lo.bin" 376 18058091803115435076
#kc_repo #kc_items_root CFSG.KD.PG10P2.accC "CFSG/Certificates/Kernel/Fi24/PG10/Slices/data/P2/tab/C_acc.bin" 395 6324122847275523048

namespace CFSG.KD.PG10P2

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 18)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 321538) (nat_lit 18)) JV loC accC i

theorem okW_all : ∀ t < 199, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 65, okC t = true := by
  kc_cover 1

end CFSG.KD.PG10P2

end
