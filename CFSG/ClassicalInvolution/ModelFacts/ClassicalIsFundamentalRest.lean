module

public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.CentralLiftE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSL
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSp

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem classicalIsFundamental_of_members' {p f : ℕ} [Fact p.Prime]
    (h : p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime), Generic.IsFundTag t →
      StatedLieAdmissible t n p e → (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
      ClassicalMembersFundamental p f t n e hp) :
    ClassicalIsFundamental p f := by
  intro hp2 hq t n e hp hFT hadm hef X _ _ ψ hψ hcen L z hL
  have : Finite (Generic.modelUniv t n p e hp).K := finite_modelUniv hp2 hp hFT hadm
  obtain ⟨L', z', hL', hmap, -⟩ := IsClassicalMember.exists_lift hp2 hq ψ hψ hcen hL
  exact ⟨L', h hp2 hq t n e hp hFT hadm hef L' z' hL', hmap.symm⟩

@[expose] def ClassicalMembersFundamentalRest (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime), Generic.IsFundTag t → t ≠ .PSL → t ≠ .PSp →
    t ≠ .PSU → StatedLieAdmissible t n p e → (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
    ClassicalMembersFundamental p f t n e hp

theorem classicalIsFundamental_of_rest {p f : ℕ} [Fact p.Prime]
    (h : ClassicalMembersFundamentalRest p f) : ClassicalIsFundamental p f := by
  refine classicalIsFundamental_of_members' fun hp2 hq t n e hp hFT hadm hef => ?_
  by_cases hL : t = .PSL
  · subst hL
    obtain rfl : e = f := hef.elim id fun h => absurd h.1 (by decide)
    exact classicalMembersFundamental_psl hp hp2 hq hadm.2.2.1
  by_cases hS : t = .PSp
  · subst hS
    obtain rfl : e = f := hef.elim id fun h => absurd h.1 (by decide)
    exact classicalMembersFundamental_psp hp hp2 hq hadm
  by_cases hU : t = .PSU
  · subst hU
    obtain rfl : e = f := hef.elim id fun h => absurd h.1 (by decide)
    exact classicalMembersFundamental_psu hp hp2 hq hadm
  exact h t n e hp hFT hL hS hU hadm hef

theorem citInductiveU_of_coreStep_rest {p f : ℕ} [Fact p.Prime] (hcore : CoreStep p f)
    (hrest : ClassicalMembersFundamentalRest p f) : CITInductiveU p f :=
  citInductiveU_of_coreStep hcore (classicalIsFundamental_of_rest hrest) (centralLift p)

end CFSG.ClassicalInvolution.ModelFacts
