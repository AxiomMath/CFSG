module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdMu

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

namespace S289

theorem isQuasisimple_of_open {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X) :
    CFSG.IsQuasisimple X :=
  ⟨⟨h.1⟩, h.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian X h⟩

section Cit3


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem lie_facts {tg : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (hFT : IsFundTag tg)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible tg n 3 1)
    (hrow : Q3NM.AutOddFreeInnerTag tg n) (h : SecIdQ8Shape (CompData.model tg n) Φ) :
    CFSG.IsQuasisimple X ∧ Q3NM.AutOddFreeInner X := by
  obtain ⟨ψ, hψ, hker, -⟩ := h
  exact ⟨isQuasisimple_of_open (Q3NM.centralQuotientData Nat.prime_three hFT hadm X ψ hψ hker).1,
    hrow Nat.prime_three hFT hadm X ψ hψ hker⟩

theorem lie_facts_of (h : SecIdLieS3 Φ ∨ SecIdLieS4 Φ) :
    CFSG.IsQuasisimple X ∧ Q3NM.AutOddFreeInner X := by
  rcases h with (h | h | h) | (h | h | h)
  · exact lie_facts (tg := .PSU) (n := 3) trivial ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      (Q3NM.autOddFreeInnerTag_of_not_D4 (by simp) (by simp)) h
  · exact lie_facts (tg := .G2) (n := 0) trivial ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩
      (Q3NM.autOddFreeInnerTag_of_not_D4 (by simp) (by simp)) h
  · exact lie_facts (tg := .trialityD4) (n := 0) trivial ⟨Nat.prime_three, le_rfl, rfl⟩
      Q3NM.autOddFreeInnerTag_trialityD4 h
  · exact lie_facts (tg := .PSU) (n := 4) trivial ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
      (Q3NM.autOddFreeInnerTag_of_not_D4 (by simp) (by simp)) h
  · exact lie_facts (tg := .POmegaOdd) (n := 3) trivial
      ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
      (Q3NM.autOddFreeInnerTag_of_not_D4 (by simp) (by simp)) h
  · exact lie_facts (tg := .POmegaMinus) (n := 4) trivial ⟨Nat.prime_three, le_rfl, le_rfl⟩
      (Q3NM.autOddFreeInnerTag_of_not_D4 (by simp) (by simp)) h

end Cit3

end S289

end CFSG.ClassicalInvolution.Q3.TL4
