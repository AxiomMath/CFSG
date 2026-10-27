module

public import CFSG.Certificates.Kernel.Bounds.HNAlt.DceSP
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.HNA.OS_0.J "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/OS_0_J.bin" 474 4102681227358077925
#kc_repo #kc_items_root CFSG.KD.HNA.OS_0.lo "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/OS_0_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.HNA.OS_0.acc "CFSG/Certificates/Kernel/Bounds/HNAlt/Data/tab/OS_0_acc.bin" 13 16557181113609755821

namespace CFSG.KD.HNA.OS_0

open CFSG.KD.HNA CFSG.KC.HNA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runSorted (pt OB) (nat_lit 15) NO
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (acc (i + 1))

@[expose] noncomputable def okn (i : Nat) : Bool := Nat.beq (sortedCount (acc (i + 1))) NO

end CFSG.KD.HNA.OS_0

#kc_each_unfold CFSG.KD.HNA.OS_0.ok 0 1 as CFSG.KD.HNA.os
  eval CFSG.KD.HNA.OS_0.lo CFSG.KD.HNA.OS_0.acc

#kc_unfold CFSG.KD.HNA.osn CFSG.KD.HNA.OS_0.okn 0 eval CFSG.KD.HNA.OS_0.acc

end
