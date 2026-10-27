module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Th.S.Data.K1_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThK1.C_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K1_C_0_J.bin" 486290 3186079641223484457
#kc_repo #kc_items_root CFSG.KD.ThK1.C_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K1_C_0_lo.bin" 93 12368583162256813137
#kc_repo #kc_items_root CFSG.KD.ThK1.C_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K1_C_0_acc.bin" 101 5968602360474327641

namespace CFSG.KD.ThK1.C_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runCover CFSG.KD.ThK1.blk CFSG.KD.ThK1.LVs (nat_lit 77723) (nat_lit 10)
      (CFSG.KC.LceSeg.seg CFSG.KD.ThK1.C_0.J (CFSG.KD.ThK1.C_0.lo (i + 1) - CFSG.KD.ThK1.C_0.lo i)
      (CFSG.KD.ThK1.C_0.lo i)) (CFSG.KD.ThK1.C_0.acc i)) (CFSG.KD.ThK1.C_0.acc (i + 1))

end CFSG.KD.ThK1.C_0

#kc_each_unfold CFSG.KD.ThK1.C_0.ok 0 16 as CFSG.KD.ThK1.sC
  eval CFSG.KD.ThK1.C_0.lo CFSG.KD.ThK1.C_0.acc

end
