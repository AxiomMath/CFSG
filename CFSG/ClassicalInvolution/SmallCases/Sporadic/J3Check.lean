module

public import Certificates.Certificate9309

public section

namespace CFSG.ClassicalInvolution

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ClassicalInvolution.J3Data

namespace J3Proof

theorem ab_check :
    ∀ h < 2, isInvA 20520 abArr[h]! abInv[h]! = true :=
  Certificates.certificate9309.1

theorem sChain_check :
    rawChainOK 20520 (sStrong.extract 0 4) sStrong sBase sDeriv 4 = true ∧
      rawOrbitSizes 20520 sStrong sBase = [128, 1, 1] :=
  Certificates.certificate9309.2.1

theorem cent_check :
    Nat.card J3Groups.K = 1920 ∧ (∀ g ∈ J3Groups.K, g * J3Groups.pa = J3Groups.pa * g) ∧
      ∀ g ∈ J3Groups.P, g * J3Groups.pa = J3Groups.pa * g → g ∈ J3Groups.K :=
  Certificates.certificate9309.2.2.1

theorem u_check :
    J3Groups.K ≤ Subgroup.normalizer (J3Groups.U : Set (Equiv.Perm (Fin 20520))) ∧
      Nat.card J3Groups.U = 32 ∧
      ∀ g ∈ J3Groups.K, (∀ u ∈ J3Groups.U, g * u = u * g) → g ∈ J3Groups.U :=
  Certificates.certificate9309.2.2.2.1

theorem cover_check :
    ∀ s ∈ J3Groups.S, orderOf s = 2 → ∃ c ∈ J3Groups.P, s = c * J3Groups.pa * c⁻¹ :=
  Certificates.certificate9309.2.2.2.2

end J3Proof

end CFSG.ClassicalInvolution
