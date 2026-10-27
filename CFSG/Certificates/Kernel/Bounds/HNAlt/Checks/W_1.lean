module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.HNA.W_1.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/W_1_J.bin" 36587 17654748401284730011
#kc_repo #kc_items_root CFSG.KD.HNA.W_1.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/W_1_lo.bin" 29 9882634931714900826
#kc_repo #kc_items_root CFSG.KD.HNA.W_1.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/W_1_acc.bin" 45 16160843944869338627

namespace CFSG.KD.HNA.W_1

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runFacts FB HB GB TB WD (nat_lit 5) (nat_lit 708) LT TL VL NL ND NO nH nT nW W Wi
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1)) (mkS NF ND) (Nat.beq i (nat_lit 4)))

end CFSG.KD.HNA.W_1

#kc_each_unfold CFSG.KD.HNA.W_1.ok 47 52 as CFSG.KD.HNA.w at 0
  eval CFSG.KD.HNA.W_1.lo CFSG.KD.HNA.W_1.acc

end
