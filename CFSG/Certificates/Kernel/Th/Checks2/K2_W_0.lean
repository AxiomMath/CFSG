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

#kc_repo #kc_items_root CFSG.KD.ThK2.W_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K2_W_0_J.bin" 2081496 15983185202714082822
#kc_repo #kc_items_root CFSG.KD.ThK2.W_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K2_W_0_lo.bin" 444 17241751024770854690
#kc_repo #kc_items_root CFSG.KD.ThK2.W_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/K2_W_0_acc.bin" 749 3404020059280052290

namespace CFSG.KD.ThK2.W_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.LceS.runFacts CFSG.KD.ThK2.blk CFSG.KD.ThK2.selWT CFSG.KD.ThK2.INV
      CFSG.KD.ThK2.nC (nat_lit 12) (CFSG.KC.LceSeg.seg CFSG.KD.ThK2.W_0.J (CFSG.KD.ThK2.W_0.lo (i +
      1) - CFSG.KD.ThK2.W_0.lo i) (CFSG.KD.ThK2.W_0.lo i)) (CFSG.KD.ThK2.W_0.acc i))
      (CFSG.KD.ThK2.W_0.acc (i + 1))

end CFSG.KD.ThK2.W_0

#kc_each_unfold CFSG.KD.ThK2.W_0.ok 0 74 as CFSG.KD.ThK2.sW
  eval CFSG.KD.ThK2.W_0.lo CFSG.KD.ThK2.W_0.acc

end
