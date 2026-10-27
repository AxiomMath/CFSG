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

#kc_repo #kc_items_root CFSG.KD.ThK3.W_2.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_W_2_J.bin" 2152245 10630767680645555995
#kc_repo #kc_items_root CFSG.KD.ThK3.W_2.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_W_2_lo.bin" 445 3587132845719041618
#kc_repo #kc_items_root CFSG.KD.ThK3.W_2.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K3_W_2_acc.bin" 825 3301432869984921344

namespace CFSG.KD.ThK3.W_2

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runFacts CFSG.KD.ThK3.blk CFSG.KD.ThK3.selWT CFSG.KD.ThK3.INV
      CFSG.KD.ThK3.nC (nat_lit 14) (CFSG.KC.LceSeg.seg CFSG.KD.ThK3.W_2.J (CFSG.KD.ThK3.W_2.lo (i +
      1 - 148) - CFSG.KD.ThK3.W_2.lo (i - 148)) (CFSG.KD.ThK3.W_2.lo (i - 148)))
      (CFSG.KD.ThK3.W_2.acc (i - 148))) (CFSG.KD.ThK3.W_2.acc (i + 1 - 148))

end CFSG.KD.ThK3.W_2

#kc_each_unfold CFSG.KD.ThK3.W_2.ok 148 222 as CFSG.KD.ThK3.sW
  eval CFSG.KD.ThK3.W_2.lo CFSG.KD.ThK3.W_2.acc

end
