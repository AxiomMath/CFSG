module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.DceS5
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
public import CFSG.Certificates.Kernel.Bounds.Core3
public import Certificates.Data.Kernel.LceSSeg
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

#kc_repo #kc_items_root CFSG.KD.LyA.S3_0.J "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S3_0_J.bin" 3027 5234336035896597411
#kc_repo #kc_items_root CFSG.KD.LyA.S3_0.lo "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S3_0_lo.bin" 9 13843742830319387364
#kc_repo #kc_items_root CFSG.KD.LyA.S3_0.acc "CFSG/Certificates/Kernel/Bounds/LyAlt/Data/tab/S3_0_acc.bin" 5 16716229469519616519

namespace CFSG.KD.LyA.S3_0

open CFSG.KD.LyA CFSG.KC.LyA.DceS CFSG.KC.LceSeg

@[expose] noncomputable def ok (i : Nat) : Bool :=
  Nat.beq (runStab FB E3 5 816 NF 3 SG3
      (seg J (lo (i + 1) - lo i) (lo i)) (acc i))
    (Bool.rec (motive := fun _ => Nat) (acc (i + 1)) (Nat.succ (bits MD 60 20)) (Nat.beq i 0))

end CFSG.KD.LyA.S3_0

#kc_each_unfold CFSG.KD.LyA.S3_0.ok 0 1 as CFSG.KD.LyA.s3
  eval CFSG.KD.LyA.S3_0.lo CFSG.KD.LyA.S3_0.acc

end
