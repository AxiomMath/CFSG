module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeMain
public import CFSG.ClassicalInvolution.SmallCases.UpgradeExcAdjoint
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalExc3

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

@[expose] def ClassicalMemberParametersRest (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ t : StatedLieTag, (t = .E7 ∨ t = .twistedE6 ∨ t = .trialityD4) →
    ClassicalMemberParametersAt p f t

theorem classicalMemberParametersExc_of_rest (h : ClassicalMemberParametersRest p f) :
    ClassicalMemberParametersExc p f := by
  intro t ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact classicalMemberParametersAt_g2
  · exact classicalMemberParametersAt_f4
  · exact classicalMemberParametersAt_e6
  · exact h _ (Or.inl rfl)
  · exact classicalMemberParametersAt_e8
  · exact h _ (Or.inr (Or.inl rfl))
  · exact h _ (Or.inr (Or.inr rfl))

theorem smallUpgrade_of_rest
    (hexc : CFSG.ClassicalInvolution.ModelFacts.ClassicalMembersFundamentalExc p f)
    (hrest : ClassicalMemberParametersRest p f) : CoreAssembly.SmallUpgrade p f :=
  smallUpgrade_of_exc hexc (classicalMemberParametersExc_of_rest hrest)

theorem smallUpgrade_of_exc2
    (hexc : CFSG.ClassicalInvolution.ModelFacts.ClassicalMembersFundamentalExc2 p f)
    (hrest : ClassicalMemberParametersRest p f) : CoreAssembly.SmallUpgrade p f :=
  smallUpgrade_of_rest (CFSG.ClassicalInvolution.ModelFacts.classicalMembersFundamentalExc_of_exc2
    hexc) hrest

end CFSG.ClassicalInvolution.Upgrade
