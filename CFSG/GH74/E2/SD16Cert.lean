
module

public import CFSG.GH74.E2.SD16CertBase

public import CFSG.GH74.E2.AutCert
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.GH74.E2.SD16CertInputs
public meta import CFSG.GH74.E2.SD16CertInputs
public import Certificates.Certificate5018

public section

namespace CFSG.GH74.E2

open CFSG.Semidihedral

section Relations

variable {M : Type*} [Group M]

end Relations

section Certificate

variable (m : ℕ)

section Decidability

variable [NeZero m]

end Decidability

end Certificate

section Instances

theorem sd16_two_involutions :
    ∃ x y : SD16M, x * x = 1 ∧ y * y = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧
    x * y = y * x ∧ x ≠ y :=
  Certificates.certificate5018.1

theorem relA_Q8 : RelA (gx 2) (gy 2) :=
  Certificates.certificate5018.2.1

theorem relB_Q8 : RelB 2 (gx 2) (gy 2) (gc 2) :=
  Certificates.certificate5018.2.2.1

theorem relC_Q8 : RelC 2 (gx 2) (gy 2) (gc 2) (gd 2) :=
  Certificates.certificate5018.2.2.2.1

theorem searchOK_Q8 : SearchOK 2 (gc 2 ^ 2) :=
  Certificates.certificate5018.2.2.2.2.1

theorem fix_SD16_Q8 : ∀ ψ : MulAut (SD16M × QuaternionGroup 2),
    ψ (gc 2 ^ 2) ∈ Subgroup.center _ → ψ (gc 2 ^ 2) = gc 2 ^ 2 :=
  fix_of_search 2 _ _ _ _ relA_Q8 relB_Q8 relC_Q8 searchOK_Q8

theorem relA_Q16 : RelA (gx 4) (gy 4) :=
  Certificates.certificate5018.2.2.2.2.2.1

theorem relB_Q16 : RelB 4 (gx 4) (gy 4) (gc 4) :=
  Certificates.certificate5018.2.2.2.2.2.2.1

theorem relC_Q16 : RelC 4 (gx 4) (gy 4) (gc 4) (gd 4) :=
  Certificates.certificate5018.2.2.2.2.2.2.2.1

theorem searchOK_Q16 : SearchOK 4 (gc 4 ^ 4) :=
  Certificates.certificate5018.2.2.2.2.2.2.2.2

theorem fix_SD16_Q16 : ∀ ψ : MulAut (SD16M × QuaternionGroup 4),
    ψ (gc 4 ^ 4) ∈ Subgroup.center _ → ψ (gc 4 ^ 4) = gc 4 ^ 4 :=
  fix_of_search 4 _ _ _ _ relA_Q16 relB_Q16 relC_Q16 searchOK_Q16

end Instances

end CFSG.GH74.E2
