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

#kc_repo #kc_items_root CFSG.KD.ThA.W_2.J "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_W_2_J.bin" 206817 3467015514776340024
#kc_repo #kc_items_root CFSG.KD.ThA.W_2.lo "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_W_2_lo.bin" 129 807709050999927259
#kc_repo #kc_items_root CFSG.KD.ThA.W_2.acc "CFSG/Certificates/Kernel/Th/Checks2/data/tab/DA_W_2_acc.bin" 216 8342325721255993425

namespace CFSG.KD.ThA.W_2

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Th.DceS.runFacts CFSG.KD.ThA.FB CFSG.KD.ThA.HB CFSG.KD.ThA.GB CFSG.KD.ThA.TB
      CFSG.KD.ThA.WD (nat_lit 4) (nat_lit 2336) CFSG.KD.ThA.LT CFSG.KD.ThA.TL CFSG.KD.ThA.VL
      CFSG.KD.ThA.NL CFSG.KD.ThA.ND CFSG.KD.ThA.NO CFSG.KD.ThA.nH CFSG.KD.ThA.nT CFSG.KD.ThA.nW
      CFSG.KD.ThA.W CFSG.KD.ThA.Wi true (CFSG.KC.LceSeg.seg CFSG.KD.ThA.W_2.J (CFSG.KD.ThA.W_2.lo (i
      + 1 - 96) - CFSG.KD.ThA.W_2.lo (i - 96)) (CFSG.KD.ThA.W_2.lo (i - 96))) (CFSG.KD.ThA.W_2.acc
      (i - 96))) (Bool.rec (motive := fun _ => Nat) (CFSG.KD.ThA.W_2.acc (i + 1 - 96))
      (CFSG.KC.Th.DceS.mkS CFSG.KD.ThA.NF CFSG.KD.ThA.ND) (Nat.beq i (nat_lit 119)))

end CFSG.KD.ThA.W_2

#kc_each_unfold CFSG.KD.ThA.W_2.ok 96 120 as CFSG.KD.ThA.w
  eval CFSG.KD.ThA.W_2.lo CFSG.KD.ThA.W_2.acc

end
