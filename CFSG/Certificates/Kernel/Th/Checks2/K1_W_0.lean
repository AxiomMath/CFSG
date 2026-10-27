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

#kc_repo #kc_items_root CFSG.KD.ThK1.W_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K1_W_0_J.bin" 1043028 5906101429908239830
#kc_repo #kc_items_root CFSG.KD.ThK1.W_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K1_W_0_lo.bin" 223 12159071767571359071
#kc_repo #kc_items_root CFSG.KD.ThK1.W_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K1_W_0_acc.bin" 379 16553696286781477911

namespace CFSG.KD.ThK1.W_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runFacts CFSG.KD.ThK1.blk CFSG.KD.ThK1.selWT CFSG.KD.ThK1.INV
      CFSG.KD.ThK1.nC (nat_lit 10) (CFSG.KC.LceSeg.seg CFSG.KD.ThK1.W_0.J (CFSG.KD.ThK1.W_0.lo (i +
      1) - CFSG.KD.ThK1.W_0.lo i) (CFSG.KD.ThK1.W_0.lo i)) (CFSG.KD.ThK1.W_0.acc i))
      (CFSG.KD.ThK1.W_0.acc (i + 1))

end CFSG.KD.ThK1.W_0

#kc_each_unfold CFSG.KD.ThK1.W_0.ok 0 37 as CFSG.KD.ThK1.sW
  eval CFSG.KD.ThK1.W_0.lo CFSG.KD.ThK1.W_0.acc

end
