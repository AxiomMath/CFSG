module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Reduce
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Toral
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.NonToral

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix MatrixGroups

theorem pPrimeGenAt_psl_three (hB : CFSG.RankThree.PartOne.ExtBloomMitchell)
    (hA6 : CFSG.RankThree.PartOne.N1322.KF1322ThreeA6Norm) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q) : PPrimeGenAt p PSL(3, ZMod q) := by
  refine pPrimeGenAt_psl_three_of hq2 hp hp2 hpq fun A hA => ?_
  by_cases hc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g
  · exact closure_fixSetThree_of_commute hp hp2 hpq hA hc
  · push Not at hc
    exact closure_fixSetThree_of_not_commute hB hA6 hq2 hp hp2 hpq hA hc

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
