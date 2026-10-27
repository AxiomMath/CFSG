
module

public import CFSG.GH74.E2.D8CertBase

public import CFSG.GH74.E2.SD16Cert
public meta import Mathlib
public import CFSG.GH74.E2.D8CertInputs
public meta import CFSG.GH74.E2.D8CertInputs
public import Certificates.Certificate5008

public section

namespace CFSG.GH74.E2

section Instances

theorem d8_searches :
    D8SearchOK 2 (d8c 2 ^ 2) ∧ D8SearchOK 4 (d8c 4 ^ 4) :=
  Certificates.certificate5008

theorem fix_D8_Q8 : ∀ ψ : MulAut (D8M × QuaternionGroup 2),
    ψ (d8c 2 ^ 2) ∈ Subgroup.center _ → ψ (d8c 2 ^ 2) = d8c 2 ^ 2 :=
  fix_of_search_D8 2 _ _ _ _ d8relA_Q8 d8relB_Q8 d8relC_Q8 d8_searches.1

theorem fix_D8_Q16 : ∀ ψ : MulAut (D8M × QuaternionGroup 4),
    ψ (d8c 4 ^ 4) ∈ Subgroup.center _ → ψ (d8c 4 ^ 4) = d8c 4 ^ 4 :=
  fix_of_search_D8 4 _ _ _ _ d8relA_Q16 d8relB_Q16 d8relC_Q16 d8_searches.2

theorem fix_D8_quat {m : ℕ} [NeZero m] (hm : m = 2 ∨ m = 4) :
    ∀ ψ : MulAut (D8M × QuaternionGroup m),
      ψ (1, QuaternionGroup.a (m : ZMod (2 * m))) ∈ Subgroup.center _ →
        ψ (1, QuaternionGroup.a (m : ZMod (2 * m))) =
          (1, QuaternionGroup.a (m : ZMod (2 * m))) := by
  rcases hm with rfl | rfl
  · have h : d8c 2 ^ 2 = (1, QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2))) :=
      Prod.ext (by simp [d8c]) (by simp only [d8c, Prod.pow_snd]; decide)
    rw [← h]
    exact fix_D8_Q8
  · have h : d8c 4 ^ 4 = (1, QuaternionGroup.a ((4 : ℕ) : ZMod (2 * 4))) :=
      Prod.ext (by simp [d8c]) (by simp only [d8c, Prod.pow_snd]; decide)
    rw [← h]
    exact fix_D8_Q16

end Instances

end CFSG.GH74.E2
