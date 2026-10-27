module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DA_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThA.ES2_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_ES2_0_J.bin" 29406 9348113544486714870
#kc_repo #kc_items_root CFSG.KD.ThA.ES2_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_ES2_0_lo.bin" 29 15718118940374551924
#kc_repo #kc_items_root CFSG.KD.ThA.ES2_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_ES2_0_acc.bin" 400 16446955124363581911

namespace CFSG.KD.ThA.ES2_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat CFSG.KD.ThA.E2) (nat_lit 17)
      (CFSG.KC.Th.DceS.bits CFSG.KD.ThA.MD (nat_lit 40) (nat_lit 20)) (CFSG.KC.LceSeg.seg
      CFSG.KD.ThA.ES2_0.J (CFSG.KD.ThA.ES2_0.lo (i + 1) - CFSG.KD.ThA.ES2_0.lo i)
      (CFSG.KD.ThA.ES2_0.lo i)) (CFSG.KD.ThA.ES2_0.acc i)) (CFSG.KD.ThA.ES2_0.acc (i + 1))

@[expose] noncomputable def count0 (_ : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThA.ES2_0.acc (nat_lit 5))) (CFSG.KC.Th.DceS.bits
      CFSG.KD.ThA.MD (nat_lit 40) (nat_lit 20))

end CFSG.KD.ThA.ES2_0

#kc_each_unfold CFSG.KD.ThA.ES2_0.ok 0 5 as CFSG.KD.ThA.es2
  eval CFSG.KD.ThA.ES2_0.lo CFSG.KD.ThA.ES2_0.acc

#kc_unfold CFSG.KD.ThA.es2n CFSG.KD.ThA.ES2_0.count0 0 eval CFSG.KD.ThA.ES2_0.acc

end
