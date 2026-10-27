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

#kc_repo #kc_items_root CFSG.KD.ThB.OS_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_OS_0_J.bin" 32284 10913134502902461511
#kc_repo #kc_items_root CFSG.KD.ThB.OS_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_OS_0_lo.bin" 34 16295150566592606098
#kc_repo #kc_items_root CFSG.KD.ThB.OS_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_OS_0_acc.bin" 65 5407190855843919915

namespace CFSG.KD.ThB.OS_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.pt CFSG.KD.ThB.OB CFSG.KD.ThB.osh
      CFSG.KD.ThB.owd CFSG.KD.ThB.om) (nat_lit 15) CFSG.KD.ThB.NO (CFSG.KC.LceSeg.seg
      CFSG.KD.ThB.OS_0.J (CFSG.KD.ThB.OS_0.lo (i + 1) - CFSG.KD.ThB.OS_0.lo i) (CFSG.KD.ThB.OS_0.lo
      i)) (CFSG.KD.ThB.OS_0.acc i)) (CFSG.KD.ThB.OS_0.acc (i + 1))

@[expose] noncomputable def count0 (_ : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThB.OS_0.acc (nat_lit 6))) CFSG.KD.ThB.NO

end CFSG.KD.ThB.OS_0

#kc_each_unfold CFSG.KD.ThB.OS_0.ok 0 6 as CFSG.KD.ThB.os
  eval CFSG.KD.ThB.OS_0.lo CFSG.KD.ThB.OS_0.acc

#kc_unfold CFSG.KD.ThB.osn CFSG.KD.ThB.OS_0.count0 0 eval CFSG.KD.ThB.OS_0.acc

end
