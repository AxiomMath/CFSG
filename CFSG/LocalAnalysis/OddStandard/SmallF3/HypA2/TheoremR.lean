module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndDispatch
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndRankQuat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SylowCases
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndData

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem false_of_endData (hAlt : CFSG.OddStandard.AltStdCyclicBalancedFalse)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hEven : EvenResidualStd) (hCTSS : CTSSStd)
    (hL2 : CFSG.Yardstones.M0362f3a873a3.OddLieThm187bResidualL2Ree) (hI : Phase1Inputs)
    (hA7 : TwoA7RankOne) (hP : Phase2Inputs) (hL : Leaves2) {G : Type} [Group G] [Finite G]
    {x : G} {Y : Subgroup G} (hY : EndData G x Y) : False := by
  haveI := hY.setting.simple
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer (Y : Set G))) := inferInstance
  rcases sylow_rank_cases (Subgroup.centralizer (Y : Set G)) S with h2 | hcyc | ⟨r, hr, e⟩
  · exact false_of_rank_two hP.rankTwo hY h2
  · rcases hY.inS with hA | hB
    · exact false_of_inSA hAlt hEven hCTSS hP hL hI hA7 hY hA S hcyc
    · exact false_of_inSB hL2 hL hI hA7 hY hB S hcyc
  · exact false_of_quaternion (hP.quat hCIT) hY S hr e

theorem false_of_residual_component_of_inputs
    (hAlt : CFSG.OddStandard.AltStdCyclicBalancedFalse)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hEven : EvenResidualStd) (hCTSS : CTSSStd)
    (hL2 : CFSG.Yardstones.M0362f3a873a3.OddLieThm187bResidualL2Ree) (hI : Phase1Inputs)
    (hA7 : TwoA7RankOne) (hP : Phase2Inputs) (hL : Leaves2) {G : Type} [Group G] [Finite G]
    (hG : HSetting G) {y : G} (hy : orderOf y = 2) {K : Subgroup G}
    (hK : Omega.IsComponentIn K (centralizer ({y} : Set G))) (hres : IsResidualA2 ↥K) :
    False := by
  obtain ⟨x, Y, hY⟩ := exists_endData hI hA7 hP hL hG hy hK hres
  exact false_of_endData hAlt hCIT hEven hCTSS hL2 hI hA7 hP hL hY

end CFSG.OddStandard.SmallF3.HypA2
