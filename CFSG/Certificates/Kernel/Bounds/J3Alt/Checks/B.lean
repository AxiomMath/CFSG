module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Data.B_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Cover

public section

#kc_repo #kc_items_root CFSG.KD.J3AB.loF "CFSG/Certificates/Kernel/Bounds/J3Alt/Data/B/tab/facts_lo.bin" 146 2068778648605107818
#kc_repo #kc_items_root CFSG.KD.J3AB.accF "CFSG/Certificates/Kernel/Bounds/J3Alt/Data/B/tab/facts_acc.bin" 249 13065452623948695402
#kc_repo #kc_items_root CFSG.KD.J3AB.JF "CFSG/Certificates/Kernel/Bounds/J3Alt/Data/B/tab/JF.bin" 664348 275231389508949807
#kc_repo #kc_items_root CFSG.KD.J3AB.loC "CFSG/Certificates/Kernel/Bounds/J3Alt/Data/B/tab/cover_lo.bin" 26 5805654318606859096
#kc_repo #kc_items_root CFSG.KD.J3AB.accC "CFSG/Certificates/Kernel/Bounds/J3Alt/Data/B/tab/cover_acc.bin" 29 8106920917460422143
#kc_repo #kc_items_root CFSG.KD.J3AB.JV "CFSG/Certificates/Kernel/Bounds/J3Alt/Data/B/tab/JV.bin" 67280 11410978820933770074

namespace CFSG.KD.J3AB

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 4)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 34242) (nat_lit 4)) JV loC accC i

theorem okW_all : ∀ t < 24, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 4, okC t = true := by
  kc_cover 1

end CFSG.KD.J3AB

end
