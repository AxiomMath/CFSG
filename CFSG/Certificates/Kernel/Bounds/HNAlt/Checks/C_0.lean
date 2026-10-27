module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.HNA.C_0.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/C_0_J.bin" 52617 4097819699125658355
#kc_repo #kc_items_root CFSG.KD.HNA.C_0.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/C_0_lo.bin" 104 6245429891002548572
#kc_repo #kc_items_root CFSG.KD.HNA.C_0.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/C_0_acc.bin" 162 10636528082353357880

namespace CFSG.KD.HNA.C_0

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runCover FB OB (nat_lit 5) (nat_lit 708) NF NO AL
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

end CFSG.KD.HNA.C_0

#kc_each_unfold CFSG.KD.HNA.C_0.ok 0 20 as CFSG.KD.HNA.c
  eval CFSG.KD.HNA.C_0.lo CFSG.KD.HNA.C_0.acc

end
