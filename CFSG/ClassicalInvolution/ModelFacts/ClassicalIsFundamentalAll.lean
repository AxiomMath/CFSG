module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalExc3
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem classicalMembersFundamentalExc2 : ClassicalMembersFundamentalExc2 p f := by
  intro hp2 hq t n e hp _ hexc hadm hef
  rcases hexc with rfl | rfl
  · obtain rfl : e = f := hef.elim id fun h' => absurd h'.1 (by decide)
    exact classicalMembersFundamental_twistedE6 hp hp2 hq hadm
  · exact classicalMembersFundamental_trialityD4 hp hp2 hq hadm
      (hef.elim Or.inl fun h' => Or.inr h'.2)

theorem classicalMembersFundamentalExc3 : ClassicalMembersFundamentalExc3 p f :=
  classicalMembersFundamentalExc3_of_exc2 classicalMembersFundamentalExc2

theorem classicalMembersFundamentalExc : ClassicalMembersFundamentalExc p f :=
  classicalMembersFundamentalExc_of_exc2 classicalMembersFundamentalExc2

end CFSG.ClassicalInvolution.ModelFacts
