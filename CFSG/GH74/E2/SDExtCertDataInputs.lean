module

public import CFSG.GH74.E2.SDExtGeneric
public import CFSG.GH74.E2.Ext2
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public meta import CFSG.GH74.E2.SDExtGeneric
public import CFSG.GH74.E2.SDExtCertInputs
public meta import CFSG.GH74.E2.SDExtCertInputs
public import Certificates.Certificate5019
public import CFSG.Sporadic.Schreier.J4SFrattini
public import CFSG.GH74.E2.SD16Cert

public section

namespace CFSG.GH74.E2

open CFSG.Semidihedral

namespace SDW

attribute [local instance] CFSG.GH74.E2.SDW.instDecEqSD16MForCert

abbrev M16 : Type := SD16M × SD16M

theorem sd16Nf_spec :
    ∀ a : SD16M, sd16R ^ (sd16Nf a).1 * sd16S ^ (sd16Nf a).2 = a :=
  Certificates.certificate5019.1

theorem sd16_relations :
    sd16R ^ 8 = 1 ∧ sd16R ^ 4 ≠ 1 ∧ sd16S * sd16S = 1 ∧ sd16S ≠ 1 ∧
    sd16S * sd16R * sd16S⁻¹ = sd16R ^ 3 :=
  Certificates.certificate5019.2.1

@[expose] def sd16Data : SDData SD16M where
  R := sd16R
  S := sd16S
  nf := sd16Nf
  nf_spec := sd16Nf_spec
  hR8 := sd16_relations.1
  hR4 := sd16_relations.2.1
  hSS := sd16_relations.2.2.1
  hS1 := sd16_relations.2.2.2.1
  hSR := sd16_relations.2.2.2.2

@[expose] def lstA : List M16 := lstSD.map fun a => (a, 1)

@[expose] def candA (x₁ x₂ : M16) : List SD16M :=
  lstSD.filter fun a =>
    decide (x₁.2 = 1 ∧ x₂.2 = 1 ∧ a * sd16R * a⁻¹ = x₁.1 ∧ a * sd16S * a⁻¹ = x₂.1)

@[expose] def candB (x₃ x₄ : M16) : List SD16M :=
  lstSD.filter fun b =>
    decide (x₃.1 = 1 ∧ x₄.1 = 1 ∧ b * sd16R * b⁻¹ = x₃.2 ∧ b * sd16S * b⁻¹ = x₄.2)

@[expose] def WitIn (b : SD16M) (y : M16) : Prop :=
  ∀ a ∈ lstSD, (((a, 1) : M16) * y = y * (a, 1)) ∧ (((a, 1) : M16) * y = 1 → a = 1 ∧ b = 1)

@[expose] def WitL (h₁ h₂ h₃ h₄ w m : M16) : Prop :=
  m * sd16Data.evA h₁ h₂ h₃ h₄ m * w = 1 ∧
    ∀ b ∈ lstSD, WitIn b (m * sd16Data.ap h₁ h₂ b * m⁻¹)

@[expose] def CertW (h₁ h₂ h₃ h₄ w : M16) : Prop :=
  sd16Data.CFix h₁ h₂ h₃ h₄ w → ∃ m ∈ lstA, WitL h₁ h₂ h₃ h₄ w m

@[expose] def CertTuple (h : M16 × M16 × M16 × M16) : Prop :=
  ∀ a ∈ candA (sd16Data.evA h.1 h.2.1 h.2.2.1 h.2.2.2 h.1)
      (sd16Data.evA h.1 h.2.1 h.2.2.1 h.2.2.2 h.2.1),
    ∀ b ∈ candB (sd16Data.evA h.1 h.2.1 h.2.2.1 h.2.2.2 h.2.2.1)
      (sd16Data.evA h.1 h.2.1 h.2.2.1 h.2.2.2 h.2.2.2),
      CertW h.1 h.2.1 h.2.2.1 h.2.2.2 (a, b)

section Decidability

instance (b : SD16M) (y : M16) : Decidable (WitIn b y) :=
  inferInstanceAs (Decidable (∀ a ∈ lstSD, _ ∧ (_ → _ ∧ _)))

instance
    (h₁ h₂ h₃ h₄ w m : M16) : Decidable (WitL h₁ h₂ h₃ h₄ w m) :=
  inferInstanceAs (Decidable (_ ∧ ∀ b ∈ lstSD, WitIn b _))

instance
    (h₁ h₂ h₃ h₄ w : M16) : Decidable (sd16Data.CFix h₁ h₂ h₃ h₄ w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance (h₁ h₂ h₃ h₄ w : M16) : Decidable (CertW h₁ h₂ h₃ h₄ w) :=
  inferInstanceAs (Decidable (_ → ∃ m ∈ lstA, _))

instance (h : M16 × M16 × M16 × M16) : Decidable (CertTuple h) :=
  inferInstanceAs (Decidable (∀ a ∈ _, ∀ b ∈ _, _))

end Decidability

end SDW

end CFSG.GH74.E2
