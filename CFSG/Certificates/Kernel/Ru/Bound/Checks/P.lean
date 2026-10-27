module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Ru.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Cover

public section

#kc_repo #kc_items_root CFSG.KD.RuBP.loF "CFSG/Certificates/Kernel/Ru/Bound/Checks/data/P/tab/facts_lo.bin" 295 10934728746536156743
#kc_repo #kc_items_root CFSG.KD.RuBP.accF "CFSG/Certificates/Kernel/Ru/Bound/Checks/data/P/tab/facts_acc.bin" 499 5523875758574059717
#kc_repo #kc_items_root CFSG.KD.RuBP.JF "CFSG/Certificates/Kernel/Ru/Bound/Checks/data/P/tab/JF.bin" 1376761 16716058859913707772
#kc_repo #kc_items_root CFSG.KD.RuBP.loC "CFSG/Certificates/Kernel/Ru/Bound/Checks/data/P/tab/cover_lo.bin" 55 10080423179562401616
#kc_repo #kc_items_root CFSG.KD.RuBP.accC "CFSG/Certificates/Kernel/Ru/Bound/Checks/data/P/tab/cover_acc.bin" 59 13524460958915836074
#kc_repo #kc_items_root CFSG.KD.RuBP.JV "CFSG/Certificates/Kernel/Ru/Bound/Checks/data/P/tab/JV.bin" 199085 1352211612416055091

namespace CFSG.KD.RuBP

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 6)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 86823) (nat_lit 6)) JV loC accC i

theorem okW_all : ∀ t < 49, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 9, okC t = true := by
  kc_cover 1

end CFSG.KD.RuBP

end
