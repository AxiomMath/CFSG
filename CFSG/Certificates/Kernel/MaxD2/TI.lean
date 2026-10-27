module

public import CFSG.Certificates.Kernel.MaxD2.Max
public import Certificates.Data.MaxD2TI

public section

namespace CFSG.KS.MaxD2

open CFSG.PSL3Four.Native Certificates.MaxD2Perm

theorem checkTI_of {D : Data} {K : Pk} (H : Hyps D K)
    (hp : ∀ i, 0 < i → i < K.nr → K.CN i % D.p ≠ 0) : Certificates.MaxD2TI.checkTI D = true := by
  unfold Certificates.MaxD2TI.checkTI
  refine allBelow_iff'.2 fun i hi => ?_
  have hi1 : i + 1 < K.nr := by rw [H.hRn]; omega
  rw [conjCount_eq H.toM hi1, if_neg (Nat.succ_ne_zero i)]
  simpa using hp (i + 1) (Nat.succ_pos i) hi1

end CFSG.KS.MaxD2

end
