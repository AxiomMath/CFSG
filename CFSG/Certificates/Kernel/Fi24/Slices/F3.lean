module

public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Bounds.Core3
public import CFSG.Certificates.Kernel.Fi24.Data.F3_Sel
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KD.F3.JF "CFSG/Certificates/Kernel/Fi24/Slices/data/F3/tab/W_0.bin" 9237217 15758651853182762635
#kc_repo #kc_items_root CFSG.KD.F3.loF "CFSG/Certificates/Kernel/Fi24/Slices/data/F3/tab/W_lo.bin" 1878 11709780761120709714
#kc_repo #kc_items_root CFSG.KD.F3.accF "CFSG/Certificates/Kernel/Fi24/Slices/data/F3/tab/W_acc.bin" 3138 9922627156724979062
#kc_repo #kc_items_root CFSG.KD.F3.JV "CFSG/Certificates/Kernel/Fi24/Slices/data/F3/tab/C_0.bin" 2054284 9419104896690336323
#kc_repo #kc_items_root CFSG.KD.F3.loC "CFSG/Certificates/Kernel/Fi24/Slices/data/F3/tab/C_lo.bin" 394 6936488770595183777
#kc_repo #kc_items_root CFSG.KD.F3.accC "CFSG/Certificates/Kernel/Fi24/Slices/data/F3/tab/C_acc.bin" 407 3082187781886436201

namespace CFSG.KD.F3

open CFSG.KC CFSG.KC.LceSeg

@[expose] noncomputable def okW (i : Nat) : Bool :=
  slOK (LceS.runFacts blk selWT INV nC (nat_lit 18)) JF loF accF i

@[expose] noncomputable def okC (i : Nat) : Bool :=
  slOK (LceS.runCover blk LVs (nat_lit 524405) (nat_lit 18)) JV loC accC i

theorem okW_all : ∀ t < 313, okW t = true := by
  kc_cover 1

theorem okC_all : ∀ t < 67, okC t = true := by
  kc_cover 1

end CFSG.KD.F3

end
