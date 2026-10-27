module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsLinear
public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsSymplectic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsUnitary
public import CFSG.ClassicalInvolution.SmallCases.UpgradeParamsOrthogonal

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

@[expose] def ClassicalMemberParametersExc (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ t : StatedLieTag,
    (t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4) →
    ClassicalMemberParametersAt p f t

theorem classicalMemberParameters_of_exc (h : ClassicalMemberParametersExc p f) :
    ClassicalMemberParameters p f := by
  intro t hFT
  by_cases hL : t = .PSL
  · subst hL
    exact classicalMemberParametersAt_psl
  by_cases hS : t = .PSp
  · subst hS
    exact classicalMemberParametersAt_psp
  by_cases hU : t = .PSU
  · subst hU
    exact classicalMemberParametersAt_psu
  by_cases hO : t = .POmegaOdd
  · subst hO
    exact classicalMemberParametersAt_pOmegaOdd
  by_cases hP : t = .POmegaPlus
  · subst hP
    exact classicalMemberParametersAt_pOmegaPlus
  by_cases hM : t = .POmegaMinus
  · subst hM
    exact classicalMemberParametersAt_pOmegaMinus
  refine h t ?_
  cases t <;> simp_all [IsFundTag]

theorem smallUpgrade_of_exc
    (hexc : CFSG.ClassicalInvolution.ModelFacts.ClassicalMembersFundamentalExc p f)
    (hpar : ClassicalMemberParametersExc p f) : CoreAssembly.SmallUpgrade p f :=
  smallUpgrade_of_exc_cover hexc lieModelCentralCover (classicalMemberParameters_of_exc hpar)

end CFSG.ClassicalInvolution.Upgrade
