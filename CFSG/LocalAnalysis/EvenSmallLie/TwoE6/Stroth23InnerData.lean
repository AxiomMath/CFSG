module

public import Certificates.Certificate3182
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open CFSG.Monster.B.TwoA.Unitary

theorem cycD_sigma : xorSel vecD 3112 = 6144 :=
  Certificates.certificate3182.1

theorem cycD_gen0 : ∀ i < 21,
    CFSG.Monster.B.Co2.Native.actD 22 n6RowArr[0]! (vecD i) = xorSel vecD gen0D[i]! :=
  Certificates.certificate3182.2.1

theorem RD_lt : ∀ j < 21, ∀ t < 22, (RD[j]!)[t]! < 2 ^ 22 :=
  Certificates.certificate3182.2.2.1

theorem checkD_twist :
    ∀ n < 2 ^ 22, CFSG.Monster.B.Co2.Native.actD 22 SD n = 6144 →
    ∃ i < 21, xorSel (fun j => CFSG.Monster.B.Co2.Native.actD 22 RD[j]! n) gen0D[i]! ≠
      CFSG.Monster.B.Co2.Native.actD 22 n6RowArr[0]!
        (CFSG.Monster.B.Co2.Native.actD 22 RD[i]! n) :=
  Certificates.certificate3182.2.2.2.1

theorem cycI_sigma : xorSel vecI 3989 = 6144 :=
  Certificates.certificate3182.2.2.2.2.1

theorem cycI_gen0 : ∀ i < 21,
    CFSG.Monster.B.Co2.Native.actD 22 n6RowArr[0]! (vecI i) = xorSel vecI gen0I[i]! :=
  Certificates.certificate3182.2.2.2.2.2.1

theorem RI_lt : ∀ j < 21, ∀ t < 22, (RI[j]!)[t]! < 2 ^ 22 :=
  Certificates.certificate3182.2.2.2.2.2.2.1

theorem checkI_unique :
    ∀ n < 2 ^ 22, CFSG.Monster.B.Co2.Native.actD 22 SI n = 6144 →
    (∀ i < 21, xorSel (fun j => CFSG.Monster.B.Co2.Native.actD 22 RI[j]! n) gen0I[i]! =
      CFSG.Monster.B.Co2.Native.actD 22 n6RowArr[0]!
        (CFSG.Monster.B.Co2.Native.actD 22 RI[i]! n)) → n = 714762 :=
  Certificates.certificate3182.2.2.2.2.2.2.2.2.1

theorem u20Basis_eq_xorSel :
    ∀ t < 20, xorSel vecI u20MaskI[t]! = u20Basis[t]! :=
  Certificates.certificate3182.2.2.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
