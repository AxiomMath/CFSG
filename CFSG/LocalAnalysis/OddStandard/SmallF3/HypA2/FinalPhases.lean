module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TheoremR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Theorem0

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem noResidualA2_of_inputs (hAlt : CFSG.OddStandard.AltStdCyclicBalancedFalse)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hEven : EvenResidualStd) (hCTSS : CTSSStd)
    (hL2 : CFSG.Yardstones.M0362f3a873a3.OddLieThm187bResidualL2Ree) (hI : Phase1Inputs)
    (hA7 : TwoA7RankOne) (hP : Phase2Inputs) (hL : Leaves2) {G : Type} [Group G] [Finite G]
    (hG : HSetting G) : NoResidualA2 G := by
  intro x y X K hcfg _ hres
  have hK : Omega.IsComponentIn K (centralizer ({y} : Set G)) :=
    (a2Config_cases (hG.balanced y hcfg.oy) hcfg).1
  exact false_of_residual_component_of_inputs hAlt hCIT hEven hCTSS hL2 hI hA7 hP hL hG hcfg.oy
    hK hres

theorem smallF3OmegaV_of_phases (hAlt : CFSG.OddStandard.AltStdCyclicBalancedFalse)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hEven : EvenResidualStd) (hCTSS : CTSSStd)
    (hL2 : CFSG.Yardstones.M0362f3a873a3.OddLieThm187bResidualL2Ree) (hI : Phase1Inputs)
    (hP : Phase2Inputs) (hL1 : Leaves1) (hL2' : Leaves2) : Omega.SmallF3OmegaV := by
  refine smallF3OmegaV_of_hypA2 fun G _ _ L hL hcat => ?_
  haveI := hL.simple
  exact hypA2_of_smallF3Cyclic hI hL1 G L hL hcat
    (noResidualA2_of_inputs hAlt hCIT hEven hCTSS hL2 hI hL1.twoA7RankOne hP hL2'
      ⟨hL.simple, hL.nonab, hL.kProper, hcat, hL.balanced⟩)

end CFSG.OddStandard.SmallF3.HypA2
