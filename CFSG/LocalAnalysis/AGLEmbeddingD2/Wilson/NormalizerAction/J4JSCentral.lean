module

public import Certificates.Certificate12606
public import CFSG.Sporadic.Schreier.J4SElevenBase1

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.GLQ CFSG.SectionRank.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem centralOK_spec :
    O.eq (mulP jsJn jsJn).1 O.one = true ∧ O.eq (mulP jsSn jsSn).1 O.one = true ∧
      O.eq (mulP jsSn jsQn).1 (mulP jsQn jsSn).1 = true := by
  have h : centralOK = true := Certificates.certificate12606
  unfold centralOK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem js_central_facts :
    (nrm₂ ^ 20) * (nrm₂ ^ 20) = 1 ∧
    ((nrm₁ ^ 2 * nrm₂ ^ 5) ^ 11) * ((nrm₁ ^ 2 * nrm₂ ^ 5) ^ 11) = 1 ∧
    ∃ a b : ℕ, a < 11 ∧ b < 11 ∧ (a ≠ 0 ∨ b ≠ 0) ∧
      ((nrm₁ ^ 2 * nrm₂ ^ 5) ^ 11) * (qx ^ a * qy ^ b) =
        (qx ^ a * qy ^ b) * ((nrm₁ ^ 2 * nrm₂ ^ 5) ^ 11) := by
  have rj := rep_powP rep_nrm₂ 20
  have rs := rep_powP (rep_mulP (rep_powP rep_nrm₁ 2) (rep_powP rep_nrm₂ 5)) 11
  have rq := rep_mulP (rep_powP rep_qx 8) (rep_powP rep_qy 4)
  refine ⟨eq_of_rep_check (rep_mulP rj rj) rep_oneP centralOK_spec.1,
    eq_of_rep_check (rep_mulP rs rs) rep_oneP centralOK_spec.2.1, 8, 4, by norm_num, by norm_num,
    Or.inl (by norm_num), ?_⟩
  have e : (nrm₁ ^ 2 * nrm₂ ^ 5) ^ 11 * (qx ^ 8 * qy ^ 4) =
      (qx ^ 8 * qy ^ 4) * (nrm₁ ^ 2 * nrm₂ ^ 5) ^ 11 :=
    eq_of_rep_check (rep_mulP rs rq) (rep_mulP rq rs) centralOK_spec.2.2
  rw [e]

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
