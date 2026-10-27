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

#kc_repo #kc_items_root CFSG.KD.ThA.W_0.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_W_0_J.bin" 376962 11656783171402600332
#kc_repo #kc_items_root CFSG.KD.ThA.W_0.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_W_0_lo.bin" 286 8449447033492636907
#kc_repo #kc_items_root CFSG.KD.ThA.W_0.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_W_0_acc.bin" 441 2833719053723992034

namespace CFSG.KD.ThA.W_0

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runFacts CFSG.KD.ThA.FB CFSG.KD.ThA.HB CFSG.KD.ThA.GB CFSG.KD.ThA.TB
      CFSG.KD.ThA.WD (nat_lit 4) (nat_lit 2336) CFSG.KD.ThA.LT CFSG.KD.ThA.TL CFSG.KD.ThA.VL
      CFSG.KD.ThA.NL CFSG.KD.ThA.ND CFSG.KD.ThA.NO CFSG.KD.ThA.nH CFSG.KD.ThA.nT CFSG.KD.ThA.nW
      CFSG.KD.ThA.W CFSG.KD.ThA.Wi true (CFSG.KC.LceSeg.seg CFSG.KD.ThA.W_0.J (CFSG.KD.ThA.W_0.lo (i
      + 1) - CFSG.KD.ThA.W_0.lo i) (CFSG.KD.ThA.W_0.lo i)) (CFSG.KD.ThA.W_0.acc i))
      (CFSG.KD.ThA.W_0.acc (i + 1))

end CFSG.KD.ThA.W_0

#kc_each_unfold CFSG.KD.ThA.W_0.ok 0 48 as CFSG.KD.ThA.w
  eval CFSG.KD.ThA.W_0.lo CFSG.KD.ThA.W_0.acc

end
