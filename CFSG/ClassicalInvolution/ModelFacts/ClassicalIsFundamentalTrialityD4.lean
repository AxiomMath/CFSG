module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Cube
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
public import CFSG.ClassicalInvolution.ModelFacts.Models

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.LieType.Steinberg.TwistedD4
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem classicalMembersFundamental_trialityD4 {n e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hadm : StatedLieAdmissible .trialityD4 n p e) (hef : e = f ∨ 3 * e = f) :
    ClassicalMembersFundamental p f .trialityD4 n e hp := by
  have he : 1 ≤ e := hadm.2.1
  have hfin' : Finite (modelUniv .trialityD4 n p e hp).K :=
    (finite_and_centralTwoSplit_modelUniv_twistedD4 hp2 hp hadm).1
  have hfin : Finite (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) := hfin'
  intro L z hL
  rcases hef with h | h
  · subst h
    obtain ⟨g, β, hβ, -, hLeq⟩ := trialityD4_exists_conj_eq_rootGroup hp2 hq he hL
    have hroot : proj β ∈ (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)).roots := by
      rw [twistedDatum_roots]
      exact isRoot_proj hβ
    exact ⟨g, proj β, Or.inr (Or.inr ⟨rfl, hroot⟩), hLeq⟩
  · subst h
    obtain ⟨g, β, hβ, -, hLeq⟩ := trialityD4_exists_conj_eq_rootGroup_cube hp2 hq he hL
    have hroot : proj β ∈ (twistedDatum (iterateFrobenius (GaloisField p (3 * e)) p e)).roots := by
      rw [twistedDatum_roots]
      exact isRoot_proj hβ
    exact ⟨g, proj β, Or.inr (Or.inr ⟨rfl, hroot⟩), hLeq⟩

end CFSG.ClassicalInvolution.ModelFacts
