module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.HNA.C_1.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/C_1_J.bin" 665 14107558811701031425
#kc_repo #kc_items_root CFSG.KD.HNA.C_1.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/C_1_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.HNA.C_1.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/C_1_acc.bin" 8 1367706949797557291

namespace CFSG.KD.HNA.C_1

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runCover FB OB (nat_lit 5) (nat_lit 708) NF NO AL
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (Nat.add (nat_lit 1) (Nat.shiftLeft ND (nat_lit 20)))

end CFSG.KD.HNA.C_1

#kc_each_unfold CFSG.KD.HNA.C_1.ok 20 21 as CFSG.KD.HNA.c at 0
  eval CFSG.KD.HNA.C_1.lo CFSG.KD.HNA.C_1.acc

end
