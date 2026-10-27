module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.P_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Cover

public section

#kc_repo #kc_items_root CFSG.KD.Fi22BP.loF "CFSG/Certificates/Kernel/Fi22/Bound/Data/P/tab/facts_lo.bin" 248 14022959389639070005
#kc_repo #kc_items_root CFSG.KD.Fi22BP.accF "CFSG/Certificates/Kernel/Fi22/Bound/Data/P/tab/facts_acc.bin" 419 11298826398090834717
#kc_repo #kc_items_root CFSG.KD.Fi22BP.JF "CFSG/Certificates/Kernel/Fi22/Bound/Data/P/tab/JF.bin" 1115922 16098073195654371979
#kc_repo #kc_items_root CFSG.KD.Fi22BP.loC "CFSG/Certificates/Kernel/Fi22/Bound/Data/P/tab/cover_lo.bin" 38 2214513442509130676
#kc_repo #kc_items_root CFSG.KD.Fi22BP.accC "CFSG/Certificates/Kernel/Fi22/Bound/Data/P/tab/cover_acc.bin" 41 15264861002784248334
#kc_repo #kc_items_root CFSG.KD.Fi22BP.JV "CFSG/Certificates/Kernel/Fi22/Bound/Data/P/tab/JV.bin" 61367 162505889943969926

namespace CFSG.KD.Fi22BP

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 4)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 82571) (nat_lit 4)) JV loC accC i

theorem okW_all : ∀ t < 41, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 6, okC t = true := by
  kc_cover 1

end CFSG.KD.Fi22BP

end
