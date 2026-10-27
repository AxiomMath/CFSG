module

public import CFSG.ClassicalInvolution.ModelFacts.CentralLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank

@[expose] def ClassicalMembersFundamental (p f : ℕ) [Fact p.Prime] (t : StatedLieTag)
    (n e : ℕ) (hp : p.Prime) : Prop :=
  ∀ (L : Subgroup (modelUniv t n p e hp).K) (z : (modelUniv t n p e hp).K),
    IsClassicalMember p f L z → L ∈ fundamentalSubgroups t (modelUniv t n p e hp).D

theorem finite_modelUniv_twistedE6 {p n e : ℕ} (hp : p.Prime) :
    Finite (modelUniv .twistedE6 n p e hp).K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Module.End (GaloisField p (2 * e))
      (Fin Minuscule.e6Data.d →₀ GaloisField p (2 * e))) :=
    Module.finite_of_finite (GaloisField p (2 * e))
  exact (inferInstance : Finite (Exceptional.twistedE6Group p e))

theorem finite_modelUniv {p n e : ℕ} {t : StatedLieTag} (hp2 : p ≠ 2) (hp : p.Prime)
    (hFT : IsFundTag t) (hadm : StatedLieAdmissible t n p e) :
    Finite (modelUniv t n p e hp).K := by
  by_cases hE : t = .twistedE6
  · subst hE
    exact finite_modelUniv_twistedE6 hp
  by_cases hD : t = .trialityD4
  · subst hD
    exact (finite_and_centralTwoSplit_modelUniv_twistedD4 hp2 hp hadm).1
  exact (finite_and_centralTwoSplit_modelUniv hp2 hp hFT hadm hE hD).1

theorem classicalIsFundamental_of_members {p f : ℕ} [Fact p.Prime]
    (h : ∀ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime), IsFundTag t →
      StatedLieAdmissible t n p e → (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
      ClassicalMembersFundamental p f t n e hp) :
    ClassicalIsFundamental p f := by
  intro hp2 hq t n e hp hFT hadm hef X _ _ ψ hψ hcen L z hL
  have : Finite (modelUniv t n p e hp).K := finite_modelUniv hp2 hp hFT hadm
  obtain ⟨L', z', hL', hmap, -⟩ := IsClassicalMember.exists_lift hp2 hq ψ hψ hcen hL
  exact ⟨L', h t n e hp hFT hadm hef L' z' hL', hmap.symm⟩

end CFSG.ClassicalInvolution.ModelFacts
