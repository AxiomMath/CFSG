module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThB.ES2_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_ES2_0_J.bin" 29406 6890274698834357115
#kc_repo #kc_items_root CFSG.KD.ThB.ES2_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_ES2_0_lo.bin" 29 15718118940374551924
#kc_repo #kc_items_root CFSG.KD.ThB.ES2_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_ES2_0_acc.bin" 400 728044457123792022

namespace CFSG.KD.ThB.ES2_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat CFSG.KD.ThB.E2) (nat_lit 17)
      (CFSG.KC.Th.DceS.bits CFSG.KD.ThB.MD (nat_lit 40) (nat_lit 20)) (CFSG.KC.LceSeg.seg
      CFSG.KD.ThB.ES2_0.J (CFSG.KD.ThB.ES2_0.lo (i + 1) - CFSG.KD.ThB.ES2_0.lo i)
      (CFSG.KD.ThB.ES2_0.lo i)) (CFSG.KD.ThB.ES2_0.acc i)) (CFSG.KD.ThB.ES2_0.acc (i + 1))

@[expose] noncomputable def count0 (_ : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThB.ES2_0.acc (nat_lit 5))) (CFSG.KC.Th.DceS.bits
      CFSG.KD.ThB.MD (nat_lit 40) (nat_lit 20))

end CFSG.KD.ThB.ES2_0

#kc_each_unfold CFSG.KD.ThB.ES2_0.ok 0 5 as CFSG.KD.ThB.es2
  eval CFSG.KD.ThB.ES2_0.lo CFSG.KD.ThB.ES2_0.acc

#kc_unfold CFSG.KD.ThB.es2n CFSG.KD.ThB.ES2_0.count0 0 eval CFSG.KD.ThB.ES2_0.acc

end
