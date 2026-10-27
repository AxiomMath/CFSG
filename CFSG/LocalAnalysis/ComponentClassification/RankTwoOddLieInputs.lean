module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieReeCover
public import CFSG.LieType.HighestRoot.GenModelsGeneric
public import CFSG.LieType.HighestRoot.CentLinearModels
public import CFSG.LieType.HighestRoot.CentSpinModels
public import CFSG.LieType.HighestRoot.CentChevalleyModels
public import CFSG.LieType.HighestRoot.CentTrialityMain
public import CFSG.LieType.HighestRoot.CentTwistedE6Three

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open CFSG.Assembly.LowTwoRank CFSG.LieType.HighestRoot
open CFSG.ClassicalInvolution.Generic (modelUniv IsFundTag)

theorem oddLieInputs_of (h3E6 : TwistedE6ThreeCZ2) : OddLieInputs where
  gen := by
    intro t n p e _ _ hfund hadm _
    exact highestRootGen_genericModelUniv t n p e Fact.out hfund hadm
  cz := by
    intro t n p e _ hp2 hfund hadm _ hG2
    cases t
    case PSL => exact highestRootCZ_genericModelUniv_PSL hp2 hadm
    case PSU => exact highestRootCZ_genericModelUniv_PSU hp2 hadm
    case PSp => exact highestRootCZ_genericModelUniv_PSp hp2 hadm
    case POmegaOdd => exact highestRootCZ_genericModelUniv_POmegaOdd hp2 hadm
    case POmegaPlus => exact highestRootCZ_genericModelUniv_POmegaPlus hp2 hadm
    case POmegaMinus => exact highestRootCZ_genericModelUniv_POmegaMinus hp2 hadm
    case G2 => exact absurd rfl hG2
    case F4 => exact highestRootCZ_modelUniv_F4 n p e hp2
    case E6 => exact highestRootCZ_modelUniv_E6 n p e hp2
    case E7 => exact highestRootCZ_modelUniv_E7 n p e hp2
    case E8 => exact highestRootCZ_modelUniv_E8 n p e hp2
    case twistedE6 => exact highestRootCZ_modelUniv_twistedE6 p e n hp2 hadm.2.1 fun _ => h3E6
    case trialityD4 => exact highestRootCZ_modelUniv_trialityD4 p e n hp2 hadm.2.1
    all_goals exact (hfund : False).elim
  g2 := by
    intro p e _ hp2 _
    exact g2InvolutionData_modelUniv p e hp2
  ree := smallReeTwoMultiplierTrivial

theorem oddLieInputs : OddLieInputs :=
  oddLieInputs_of twistedE6ThreeCZ2

end CFSG.ComponentClassification.RankTwoOddLie
