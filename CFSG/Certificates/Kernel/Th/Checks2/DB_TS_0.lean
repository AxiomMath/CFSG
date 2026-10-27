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

#kc_repo #kc_items_root CFSG.KD.ThB.TS_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_TS_0_J.bin" 78414 16405144110269539184
#kc_repo #kc_items_root CFSG.KD.ThB.TS_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_TS_0_lo.bin" 69 11534919264796099462
#kc_repo #kc_items_root CFSG.KD.ThB.TS_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DB_TS_0_acc.bin" 1032 12825997025336269883

namespace CFSG.KD.ThB.TS_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runSorted (CFSG.KC.Th.DceS.tSig CFSG.KD.ThB.HB CFSG.KD.ThB.TB) (nat_lit
      17) CFSG.KD.ThB.nT (CFSG.KC.LceSeg.seg CFSG.KD.ThB.TS_0.J (CFSG.KD.ThB.TS_0.lo (i + 1) -
      CFSG.KD.ThB.TS_0.lo i) (CFSG.KD.ThB.TS_0.lo i)) (CFSG.KD.ThB.TS_0.acc i))
      (CFSG.KD.ThB.TS_0.acc (i + 1))

@[expose] noncomputable def count0 (_ : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.sortedCount (CFSG.KD.ThB.TS_0.acc (nat_lit 13))) CFSG.KD.ThB.nT

end CFSG.KD.ThB.TS_0

#kc_each_unfold CFSG.KD.ThB.TS_0.ok 0 13 as CFSG.KD.ThB.ts
  eval CFSG.KD.ThB.TS_0.lo CFSG.KD.ThB.TS_0.acc

#kc_unfold CFSG.KD.ThB.tsn CFSG.KD.ThB.TS_0.count0 0 eval CFSG.KD.ThB.TS_0.acc

end
