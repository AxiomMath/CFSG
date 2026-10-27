module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalExc
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalF4

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

@[expose] def ClassicalMembersFundamentalExc3 (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime), Generic.IsFundTag t →
    (t = .E7 ∨ t = .twistedE6 ∨ t = .trialityD4) →
    StatedLieAdmissible t n p e → (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
    ClassicalMembersFundamental p f t n e hp

theorem classicalMembersFundamentalExc_of_exc3 {p f : ℕ} [Fact p.Prime]
    (h : ClassicalMembersFundamentalExc3 p f) : ClassicalMembersFundamentalExc p f := by
  intro hp2 hq t n e hp hFT hexc hadm hef
  by_cases h3 : t = .E7 ∨ t = .twistedE6 ∨ t = .trialityD4
  · exact h hp2 hq t n e hp hFT h3 hadm hef
  have hnot : ¬ t = .trialityD4 := fun ht => h3 (Or.inr (Or.inr ht))
  obtain rfl : e = f := hef.elim id fun h' => absurd h'.1 hnot
  rcases hexc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact classicalMembersFundamental_g2 hp hp2 hq
  · exact classicalMembersFundamental_f4 hp hp2 hq
  · exact classicalMembersFundamental_e6 hp hp2 hq hadm
  · exact absurd (Or.inl rfl) h3
  · exact classicalMembersFundamental_e8 hp hp2 hq hadm
  · exact absurd (Or.inr (Or.inl rfl)) h3
  · exact absurd (Or.inr (Or.inr rfl)) h3

theorem citInductiveU_of_coreStep_exc3 {p f : ℕ} [Fact p.Prime] (hcore : CoreStep p f)
    (h : ClassicalMembersFundamentalExc3 p f) : CITInductiveU p f :=
  citInductiveU_of_coreStep_exc hcore (classicalMembersFundamentalExc_of_exc3 h)

@[expose] def ClassicalMembersFundamentalExc2 (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (t : StatedLieTag) (n e : ℕ) (hp : p.Prime), Generic.IsFundTag t →
    (t = .twistedE6 ∨ t = .trialityD4) →
    StatedLieAdmissible t n p e → (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
    ClassicalMembersFundamental p f t n e hp

theorem classicalMembersFundamentalExc3_of_exc2 {p f : ℕ} [Fact p.Prime]
    (h : ClassicalMembersFundamentalExc2 p f) : ClassicalMembersFundamentalExc3 p f := by
  intro hp2 hq t n e hp hFT hexc hadm hef
  by_cases h7 : t = .E7
  · subst h7
    obtain rfl : e = f := hef.elim id fun h' => absurd h'.1 (by decide)
    exact classicalMembersFundamental_e7 hp hp2 hq hadm
  · exact h hp2 hq t n e hp hFT (hexc.resolve_left h7) hadm hef

theorem classicalMembersFundamentalExc_of_exc2 {p f : ℕ} [Fact p.Prime]
    (h : ClassicalMembersFundamentalExc2 p f) : ClassicalMembersFundamentalExc p f :=
  classicalMembersFundamentalExc_of_exc3 (classicalMembersFundamentalExc3_of_exc2 h)

theorem citInductiveU_of_coreStep_exc2 {p f : ℕ} [Fact p.Prime] (hcore : CoreStep p f)
    (h : ClassicalMembersFundamentalExc2 p f) : CITInductiveU p f :=
  citInductiveU_of_coreStep_exc3 hcore (classicalMembersFundamentalExc3_of_exc2 h)

end CFSG.ClassicalInvolution.ModelFacts
