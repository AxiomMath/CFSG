module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Th.S.Data.K3_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThK3.W_1.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_W_1_J.bin" 2043628 9901181625211396787
#kc_repo #kc_items_root CFSG.KD.ThK3.W_1.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_W_1_lo.bin" 444 15120948938283243785
#kc_repo #kc_items_root CFSG.KD.ThK3.W_1.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_W_1_acc.bin" 769 13695316189954530507

namespace CFSG.KD.ThK3.W_1

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runFacts CFSG.KD.ThK3.blk CFSG.KD.ThK3.selWT CFSG.KD.ThK3.INV
      CFSG.KD.ThK3.nC (nat_lit 14) (CFSG.KC.LceSeg.seg CFSG.KD.ThK3.W_1.J (CFSG.KD.ThK3.W_1.lo (i +
      1 - 74) - CFSG.KD.ThK3.W_1.lo (i - 74)) (CFSG.KD.ThK3.W_1.lo (i - 74))) (CFSG.KD.ThK3.W_1.acc
      (i - 74))) (CFSG.KD.ThK3.W_1.acc (i + 1 - 74))

end CFSG.KD.ThK3.W_1

#kc_each_unfold CFSG.KD.ThK3.W_1.ok 74 148 as CFSG.KD.ThK3.sW
  eval CFSG.KD.ThK3.W_1.lo CFSG.KD.ThK3.W_1.acc

end
