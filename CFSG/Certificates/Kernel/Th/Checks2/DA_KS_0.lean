module

public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.Data.DA_Sel
public import CFSG.Certificates.Kernel.Th.S.Data.DB_Sel
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LceSSeg
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.ThA.KS_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_KS_0_J.bin" 1030 8986186158343273816
#kc_repo #kc_items_root CFSG.KD.ThA.KS_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_KS_0_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThA.KS_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_KS_0_acc.bin" 84 1336749770218287082

namespace CFSG.KD.ThA.KS_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.mat CFSG.KD.ThA.CB) (nat_lit 10)
      CFSG.KD.ThA.NCL (CFSG.KC.LceSeg.seg CFSG.KD.ThA.KS_0.J (CFSG.KD.ThA.KS_0.lo (i + 1) -
      CFSG.KD.ThA.KS_0.lo i) (CFSG.KD.ThA.KS_0.lo i)) (CFSG.KD.ThA.KS_0.acc i))
      (CFSG.KD.ThA.KS_0.acc (i + 1))

@[expose] noncomputable def count0 (_ : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThA.KS_0.acc (nat_lit 1))) CFSG.KD.ThA.NCL

end CFSG.KD.ThA.KS_0

#kc_each_unfold CFSG.KD.ThA.KS_0.ok 0 1 as CFSG.KD.ThA.ks
  eval CFSG.KD.ThA.KS_0.lo CFSG.KD.ThA.KS_0.acc

#kc_unfold CFSG.KD.ThA.ksn CFSG.KD.ThA.KS_0.count0 0 eval CFSG.KD.ThA.KS_0.acc

end
