module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalRest
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

@[expose] def ClassicalMembersFundamentalExc (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime), Generic.IsFundTag t →
    (t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4) →
    StatedLieAdmissible t n p e → (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
    ClassicalMembersFundamental p f t n e hp

theorem classicalIsFundamental_of_exc {p f : ℕ} [Fact p.Prime]
    (h : ClassicalMembersFundamentalExc p f) : ClassicalIsFundamental p f := by
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
  by_cases hO : t = .POmegaOdd
  · subst hO
    obtain rfl : e = f := hef.elim id fun h => absurd h.1 (by decide)
    exact classicalMembersFundamental_pOmegaOdd hp hp2 hq hadm
  by_cases hP : t = .POmegaPlus
  · subst hP
    obtain rfl : e = f := hef.elim id fun h => absurd h.1 (by decide)
    exact classicalMembersFundamental_pOmegaPlus hp hp2 hq hadm
  by_cases hM : t = .POmegaMinus
  · subst hM
    obtain rfl : e = f := hef.elim id fun h => absurd h.1 (by decide)
    exact classicalMembersFundamental_pOmegaMinus hp hp2 hq hadm
  refine h hp2 hq t n e hp hFT ?_ hadm hef
  cases t <;> simp_all [Generic.IsFundTag]

theorem citInductiveU_of_coreStep_exc {p f : ℕ} [Fact p.Prime] (hcore : CoreStep p f)
    (hexc : ClassicalMembersFundamentalExc p f) : CITInductiveU p f :=
  citInductiveU_of_coreStep hcore (classicalIsFundamental_of_exc hexc) (centralLift p)

end CFSG.ClassicalInvolution.ModelFacts
