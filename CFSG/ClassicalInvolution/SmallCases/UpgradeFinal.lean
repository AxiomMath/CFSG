module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeRest
public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwD4
public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwE6
public import CFSG.ClassicalInvolution.SmallCases.UpgradeTwE7

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem classicalMemberParametersRest : ClassicalMemberParametersRest p f := by
  intro t ht
  rcases ht with rfl | rfl | rfl
  · exact classicalMemberParametersAt_e7
  · exact classicalMemberParametersAt_twistedE6
  · exact classicalMemberParametersAt_trialityD4

theorem classicalMemberParametersExc : ClassicalMemberParametersExc p f :=
  classicalMemberParametersExc_of_rest classicalMemberParametersRest

theorem classicalMemberParameters : ClassicalMemberParameters p f :=
  classicalMemberParameters_of_exc classicalMemberParametersExc

theorem smallUpgrade_of_fundamentalExc
    (hexc : CFSG.ClassicalInvolution.ModelFacts.ClassicalMembersFundamentalExc p f) :
    CoreAssembly.SmallUpgrade p f :=
  smallUpgrade_of_exc hexc classicalMemberParametersExc

theorem smallUpgrade_of_fundamentalExc2
    (hexc : CFSG.ClassicalInvolution.ModelFacts.ClassicalMembersFundamentalExc2 p f) :
    CoreAssembly.SmallUpgrade p f :=
  smallUpgrade_of_exc2 hexc classicalMemberParametersRest

end CFSG.ClassicalInvolution.Upgrade
