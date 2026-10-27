module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Th.S.Data.K2_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThK2.W_1.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K2_W_1_J.bin" 405763 11662653349031155742
#kc_repo #kc_items_root CFSG.KD.ThK2.W_1.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K2_W_1_lo.bin" 83 10218121270630855629
#kc_repo #kc_items_root CFSG.KD.ThK2.W_1.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K2_W_1_acc.bin" 150 18326900950960644412

namespace CFSG.KD.ThK2.W_1

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runFacts CFSG.KD.ThK2.blk CFSG.KD.ThK2.selWT CFSG.KD.ThK2.INV
      CFSG.KD.ThK2.nC (nat_lit 12) (CFSG.KC.LceSeg.seg CFSG.KD.ThK2.W_1.J (CFSG.KD.ThK2.W_1.lo (i +
      1 - 74) - CFSG.KD.ThK2.W_1.lo (i - 74)) (CFSG.KD.ThK2.W_1.lo (i - 74))) (CFSG.KD.ThK2.W_1.acc
      (i - 74))) (CFSG.KD.ThK2.W_1.acc (i + 1 - 74))

end CFSG.KD.ThK2.W_1

#kc_each_unfold CFSG.KD.ThK2.W_1.ok 74 88 as CFSG.KD.ThK2.sW
  eval CFSG.KD.ThK2.W_1.lo CFSG.KD.ThK2.W_1.acc

end
