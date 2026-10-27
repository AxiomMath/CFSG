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

#kc_repo #kc_items_root CFSG.KD.ThK3.W_3.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_W_3_J.bin" 2030489 9337750382958191536
#kc_repo #kc_items_root CFSG.KD.ThK3.W_3.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_W_3_lo.bin" 414 6832794165941147185
#kc_repo #kc_items_root CFSG.KD.ThK3.W_3.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_W_3_acc.bin" 770 15140181918608435650

namespace CFSG.KD.ThK3.W_3

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runFacts CFSG.KD.ThK3.blk CFSG.KD.ThK3.selWT CFSG.KD.ThK3.INV
      CFSG.KD.ThK3.nC (nat_lit 14) (CFSG.KC.LceSeg.seg CFSG.KD.ThK3.W_3.J (CFSG.KD.ThK3.W_3.lo (i +
      1 - 222) - CFSG.KD.ThK3.W_3.lo (i - 222)) (CFSG.KD.ThK3.W_3.lo (i - 222)))
      (CFSG.KD.ThK3.W_3.acc (i - 222))) (CFSG.KD.ThK3.W_3.acc (i + 1 - 222))

end CFSG.KD.ThK3.W_3

#kc_each_unfold CFSG.KD.ThK3.W_3.ok 222 291 as CFSG.KD.ThK3.sW
  eval CFSG.KD.ThK3.W_3.lo CFSG.KD.ThK3.W_3.acc

end
