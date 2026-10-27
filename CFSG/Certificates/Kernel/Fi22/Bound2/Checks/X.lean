module

public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X1_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X2_Sel
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.X3_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Cover

public section

#kc_repo #kc_items_root CFSG.KD.Fi22KX1.loF "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X1/tab/facts_lo.bin" 91 14932722595328836710
#kc_repo #kc_items_root CFSG.KD.Fi22KX1.accF "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X1/tab/facts_acc.bin" 159 8453255707242425290
#kc_repo #kc_items_root CFSG.KD.Fi22KX1.JF "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X1/tab/JF.bin" 421605 16075185119392454867
#kc_repo #kc_items_root CFSG.KD.Fi22KX1.loC "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X1/tab/cover_lo.bin" 39 5855024159224646945
#kc_repo #kc_items_root CFSG.KD.Fi22KX1.accC "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X1/tab/cover_acc.bin" 47 3417151900940939869
#kc_repo #kc_items_root CFSG.KD.Fi22KX1.JV "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X1/tab/JV.bin" 222067 6101001525686598715
#kc_repo #kc_items_root CFSG.KD.Fi22KX2.loF "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X2/tab/facts_lo.bin" 78 10158332884231249500
#kc_repo #kc_items_root CFSG.KD.Fi22KX2.accF "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X2/tab/facts_acc.bin" 139 4468958546493814645
#kc_repo #kc_items_root CFSG.KD.Fi22KX2.JF "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X2/tab/JF.bin" 357008 1328727445077389921
#kc_repo #kc_items_root CFSG.KD.Fi22KX2.loC "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X2/tab/cover_lo.bin" 29 2455014691879082850
#kc_repo #kc_items_root CFSG.KD.Fi22KX2.accC "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X2/tab/cover_acc.bin" 35 2380724697597362596
#kc_repo #kc_items_root CFSG.KD.Fi22KX2.JV "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X2/tab/JV.bin" 158911 17924349045836761126
#kc_repo #kc_items_root CFSG.KD.Fi22KX3.loF "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X3/tab/facts_lo.bin" 217 147964154316595298
#kc_repo #kc_items_root CFSG.KD.Fi22KX3.accF "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X3/tab/facts_acc.bin" 369 16356077794769655804
#kc_repo #kc_items_root CFSG.KD.Fi22KX3.JF "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X3/tab/JF.bin" 1037239 17409959878503012678
#kc_repo #kc_items_root CFSG.KD.Fi22KX3.loC "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X3/tab/cover_lo.bin" 73 15432345230229956603
#kc_repo #kc_items_root CFSG.KD.Fi22KX3.accC "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X3/tab/cover_acc.bin" 83 15942688699388747719
#kc_repo #kc_items_root CFSG.KD.Fi22KX3.JV "CFSG/Certificates/Kernel/Fi22/Bound2/Data/X3/tab/JV.bin" 388441 18417712367683036346

namespace CFSG.KD

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def Fi22KX1.okW (i : Nat) : Bool :=
  slOK (LceS.runFacts Fi22KX1.blk Fi22KX1.selWT Fi22KX1.INV Fi22KX1.nC (nat_lit 8)) Fi22KX1.JF
    Fi22KX1.loF Fi22KX1.accF i

@[expose] noncomputable def Fi22KX1.okC (i : Nat) : Bool :=
  slOK (LceS.runCover Fi22KX1.blk Fi22KX1.LVs (nat_lit 27648) (nat_lit 8)) Fi22KX1.JV Fi22KX1.loC
    Fi22KX1.accC i

@[expose] noncomputable def Fi22KX2.okW (i : Nat) : Bool :=
  slOK (LceS.runFacts Fi22KX2.blk Fi22KX2.selWT Fi22KX2.INV Fi22KX2.nC (nat_lit 10)) Fi22KX2.JF
    Fi22KX2.loF Fi22KX2.accF i

@[expose] noncomputable def Fi22KX2.okC (i : Nat) : Bool :=
  slOK (LceS.runCover Fi22KX2.blk Fi22KX2.LVs (nat_lit 20013) (nat_lit 10)) Fi22KX2.JV Fi22KX2.loC
    Fi22KX2.accC i

@[expose] noncomputable def Fi22KX3.okW (i : Nat) : Bool :=
  slOK (LceS.runFacts Fi22KX3.blk Fi22KX3.selWT Fi22KX3.INV Fi22KX3.nC (nat_lit 12)) Fi22KX3.JF
    Fi22KX3.loF Fi22KX3.accF i

@[expose] noncomputable def Fi22KX3.okC (i : Nat) : Bool :=
  slOK (LceS.runCover Fi22KX3.blk Fi22KX3.LVs (nat_lit 56235) (nat_lit 12)) Fi22KX3.JV Fi22KX3.loC
    Fi22KX3.accC i

theorem Fi22KX1.okW_all : ∀ t < 15, Fi22KX1.okW t = true := by
  kc_cover 1

theorem Fi22KX1.okC_all : ∀ t < 7, Fi22KX1.okC t = true := by
  kc_cover 1

theorem Fi22KX2.okW_all : ∀ t < 13, Fi22KX2.okW t = true := by
  kc_cover 1

theorem Fi22KX2.okC_all : ∀ t < 5, Fi22KX2.okC t = true := by
  kc_cover 1

theorem Fi22KX3.okW_all : ∀ t < 36, Fi22KX3.okW t = true := by
  kc_cover 1

theorem Fi22KX3.okC_all : ∀ t < 13, Fi22KX3.okC t = true := by
  kc_cover 1

end CFSG.KD

end
