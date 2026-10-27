module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Co2.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Cover

public section

#kc_repo #kc_items_root CFSG.KD.Co2BP.loF "CFSG/Certificates/Kernel/Co2/Bound/Checks/data/P/tab/facts_lo.bin" 1058 4441906321351378485
#kc_repo #kc_items_root CFSG.KD.Co2BP.accF "CFSG/Certificates/Kernel/Co2/Bound/Checks/data/P/tab/facts_acc.bin" 1902 15721311723608535744
#kc_repo #kc_items_root CFSG.KD.Co2BP.JF "CFSG/Certificates/Kernel/Co2/Bound/Checks/data/P/tab/JF.bin" 4935025 4897936170344819251

namespace CFSG.KD.Co2BP

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 4)) JF loF accF i

theorem okW_all : ∀ t < 176, okW t = true := by
  kc_cover 1

end CFSG.KD.Co2BP

end
