module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.Assemble
public import CFSG.LocalAnalysis.OddStandard.HigherRank.ClassicalFalseHolds
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.AsmHolds
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Case3False
public import CFSG.Milestones.ASVolI.I3Components
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LULeaf

public section

namespace CFSG.OddStandard.HigherRank

open CFSG.ComponentClassification CFSG.ComponentClassification.HarrisLit
  CFSG.Yardstones.M0362f3a873a3

theorem oddLieThm187bResidualHigherRank_of_yamadaCase3Core
    (hCI : GSLit.ClassicalInvolutionInput) (hS : GSThmB.Solomon2AnInput)
    (hLB : CFSG.Open.LBalanceStatement) (hY : G2Three.YamadaCase3Core) :
    OddLieThm187bResidualHigherRank :=
  assemble (catalogCaseHolds_of_pumpLeaf GS82PumpInputs.chevOddPumpLeaf_holds)
    (classicalFalse_of_ci hCI hS) (F3.f3HigherRankFalse_of_ci hCI hLB)
    (G2Three.g23StandardFalse_of_core (T1.harris82Theorem1KProper_of_ci hCI)
      TBLit.griessMultipliersOdd_holds CFSG.ASVolI.as_I_3_1
      ⟨T1.RowAlt.rowCore_alt, T1.RowLie.rowCore_lieOther, T1.RowSpor.rowCore_spor⟩
      CFSG.Sporadic.Mathieu.card_M11 LinUnit.pslUnitU43Leaf_holds hY)

end CFSG.OddStandard.HigherRank
