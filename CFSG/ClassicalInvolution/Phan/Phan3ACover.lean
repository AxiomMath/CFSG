module

public import Certificates.Certificate270005

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

theorem card_phanA3Group_le :
    Finite PhanA3Group ∧ Nat.card PhanA3Group ≤ 19440 * 6048 :=
  Certificates.certificate270005.1

theorem three_dvd_orderOf_phanA3 {w : List (Fin 6 × Bool)}
    (hw : (w, 3) ∈ phanA3KernelWords) :
    3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk w) : PhanA3Group) :=
  Certificates.certificate270005.2 w hw

end CFSG.ClassicalInvolution.Phan.Q3G
