module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.HNA.TS_0.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/TS_0_J.bin" 23963 1238483212897154919
#kc_repo #kc_items_root CFSG.KD.HNA.TS_0.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/TS_0_lo.bin" 24 5345327144182400672
#kc_repo #kc_items_root CFSG.KD.HNA.TS_0.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/TS_0_acc.bin" 197 2122739193477104416

namespace CFSG.KD.HNA.TS_0

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runSorted (tS TB) (nat_lit 19) nT
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

@[expose] noncomputable def okn (i : Nat) : Bool := Nat.beq (sortedCount (acc (i + 1))) nT

end CFSG.KD.HNA.TS_0

#kc_each_unfold CFSG.KD.HNA.TS_0.ok 0 4 as CFSG.KD.HNA.ts
  eval CFSG.KD.HNA.TS_0.lo CFSG.KD.HNA.TS_0.acc

#kc_unfold CFSG.KD.HNA.tsn CFSG.KD.HNA.TS_0.okn 3 eval CFSG.KD.HNA.TS_0.acc

end
