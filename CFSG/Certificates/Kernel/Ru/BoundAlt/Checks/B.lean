module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Ru.BoundAlt.Data.B_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Cover

public section

#kc_repo #kc_items_root CFSG.KD.RuBAB.loF "CFSG/Certificates/Kernel/Ru/BoundAlt/Checks/data/B/tab/facts_lo.bin" 1382 6309915511693986140
#kc_repo #kc_items_root CFSG.KD.RuBAB.accF "CFSG/Certificates/Kernel/Ru/BoundAlt/Checks/data/B/tab/facts_acc.bin" 2511 1519555904775550975
#kc_repo #kc_items_root CFSG.KD.RuBAB.JF "CFSG/Certificates/Kernel/Ru/BoundAlt/Checks/data/B/tab/JF.bin" 6473430 13552572961288228424
#kc_repo #kc_items_root CFSG.KD.RuBAB.loC "CFSG/Certificates/Kernel/Ru/BoundAlt/Checks/data/B/tab/cover_lo.bin" 142 8803905090723103488
#kc_repo #kc_items_root CFSG.KD.RuBAB.accC "CFSG/Certificates/Kernel/Ru/BoundAlt/Checks/data/B/tab/cover_acc.bin" 159 10840635617279468643
#kc_repo #kc_items_root CFSG.KD.RuBAB.JV "CFSG/Certificates/Kernel/Ru/BoundAlt/Checks/data/B/tab/JV.bin" 226807 7334657496299073245

namespace CFSG.KD.RuBAB

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 20)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 415593) (nat_lit 20)) JV loC accC i

theorem okW_all : ∀ t < 230, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 24, okC t = true := by
  kc_cover 1

end CFSG.KD.RuBAB

end
