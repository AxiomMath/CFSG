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

#kc_repo #kc_items_root CFSG.KD.ThA.OS_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_OS_0_J.bin" 15174 9557834030926927431
#kc_repo #kc_items_root CFSG.KD.ThA.OS_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_OS_0_lo.bin" 49 13319687021087572164
#kc_repo #kc_items_root CFSG.KD.ThA.OS_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_OS_0_acc.bin" 2660 14929203643773683371

namespace CFSG.KD.ThA.OS_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.pt CFSG.KD.ThA.OB CFSG.KD.ThA.osh
      CFSG.KD.ThA.owd CFSG.KD.ThA.om) (nat_lit 15) CFSG.KD.ThA.NO (CFSG.KC.LceSeg.seg
      CFSG.KD.ThA.OS_0.J (CFSG.KD.ThA.OS_0.lo (i + 1) - CFSG.KD.ThA.OS_0.lo i) (CFSG.KD.ThA.OS_0.lo
      i)) (CFSG.KD.ThA.OS_0.acc i)) (CFSG.KD.ThA.OS_0.acc (i + 1))

@[expose] noncomputable def count0 (_ : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThA.OS_0.acc (nat_lit 9))) CFSG.KD.ThA.NO

end CFSG.KD.ThA.OS_0

#kc_each_unfold CFSG.KD.ThA.OS_0.ok 0 9 as CFSG.KD.ThA.os
  eval CFSG.KD.ThA.OS_0.lo CFSG.KD.ThA.OS_0.acc

#kc_unfold CFSG.KD.ThA.osn CFSG.KD.ThA.OS_0.count0 0 eval CFSG.KD.ThA.OS_0.acc

end
