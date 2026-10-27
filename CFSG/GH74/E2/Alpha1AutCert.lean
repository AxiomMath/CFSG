module

public import CFSG.GH74.E2.Cl2Quot
public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.E2.DirectProd
public import CFSG.CharacterTheory.Semidihedral.Presentation
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public import CFSG.GH74.E2.Alpha1AutCertInputs
public meta import CFSG.GH74.E2.Alpha1AutCertInputs
public import Certificates.Certificate5004
public import CFSG.GH74.E2.SD16CertBase
public import CFSG.GH74.E2.SD16Cert

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.Semidihedral

section Certificate

variable (m : ℕ)

section Decidability

variable [NeZero m]

instance (a b : SD16M × DihedralGroup (2 * m)) : Decidable (RelA a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance (a b c : SD16M × DihedralGroup (2 * m)) : Decidable (RelB m a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (a b c d : SD16M × DihedralGroup (2 * m)) : Decidable (RelD a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (c : SD16M × DihedralGroup (2 * m)) : Decidable (DCentralPow m c) :=
  inferInstanceAs (Decidable (∀ y : SD16M × DihedralGroup (2 * m), y * c ^ m = c ^ m * y))

instance (a b c : SD16M × DihedralGroup (2 * m)) : Decidable (DSearch4 m a b c) :=
  inferInstanceAs (Decidable (∀ d : SD16M × DihedralGroup (2 * m), RelD a b c d → False))

instance (t₀ a b : SD16M × DihedralGroup (2 * m)) : Decidable (DSearch3 m t₀ a b) :=
  inferInstanceAs (Decidable (∀ c : SD16M × DihedralGroup (2 * m), RelB m a b c →
    DCentralPow m c → c ^ m ≠ t₀ → DSearch4 m a b c))

instance (t₀ a : SD16M × DihedralGroup (2 * m)) : Decidable (DSearch2 m t₀ a) :=
  inferInstanceAs (Decidable (∀ b : SD16M × DihedralGroup (2 * m), RelA a b →
    DSearch3 m t₀ a b))

instance (t₀ : SD16M × DihedralGroup (2 * m)) : Decidable (DSearchOK m t₀) :=
  inferInstanceAs (Decidable (∀ a : SD16M × DihedralGroup (2 * m), a ^ 8 = 1 →
    DSearch2 m t₀ a))

end Decidability

end Certificate

end CFSG.GH74.E2
