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

#kc_repo #kc_items_root CFSG.KD.ThA.TS_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_TS_0_J.bin" 209 7365940528821889306
#kc_repo #kc_items_root CFSG.KD.ThA.TS_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_TS_0_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.ThA.TS_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_TS_0_acc.bin" 84 14003621658881293556

namespace CFSG.KD.ThA.TS_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.tSig CFSG.KD.ThA.HB CFSG.KD.ThA.TB) (nat_lit
      17) CFSG.KD.ThA.nT (CFSG.KC.LceSeg.seg CFSG.KD.ThA.TS_0.J (CFSG.KD.ThA.TS_0.lo (i + 1) -
      CFSG.KD.ThA.TS_0.lo i) (CFSG.KD.ThA.TS_0.lo i)) (CFSG.KD.ThA.TS_0.acc i))
      (CFSG.KD.ThA.TS_0.acc (i + 1))

@[expose] noncomputable def count0 (_ : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThA.TS_0.acc (nat_lit 1))) CFSG.KD.ThA.nT

end CFSG.KD.ThA.TS_0

#kc_each_unfold CFSG.KD.ThA.TS_0.ok 0 1 as CFSG.KD.ThA.ts
  eval CFSG.KD.ThA.TS_0.lo CFSG.KD.ThA.TS_0.acc

#kc_unfold CFSG.KD.ThA.tsn CFSG.KD.ThA.TS_0.count0 0 eval CFSG.KD.ThA.TS_0.acc

end
