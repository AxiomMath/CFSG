module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndGA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2Holds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Holds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lChev3End
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lChev3Rows
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverSpinHolds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lE6Holds
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcE7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcE8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcF4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcTriality
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExceptions
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lNotChevOdd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lResidualRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowPSLThree
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowPSU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowPSp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTableC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTwoA7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTwoAnSL25

public section

namespace CFSG.OddStandard.SmallF3

open _root_.Certificates CFSG.OddStandard.SmallF3.HypA2Leaves

theorem ys09asm_leaves
    : HypA2.Leaves1 ∧ HypA2.Leaves2 := by
  have hC := chevOddInChev2_holds
  have hGr := ComponentClassification.TBLit.griessMultipliersOdd_holds
  have hSchur := Alternating.Multipliers.schurAlternatingMultiplierInput
  have hO := ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hCl2 := a2l_cl2_holds
  have hRows : a2lRows :=
    ⟨a2l_rowPSL hC, a2l_rowPSU hC, a2l_rowPSp, a2l_rowPOmegaOdd hC, a2l_rowPOmegaPlus hC,
      a2l_rowPOmegaMinus hC, a2lRowG2_holds, a2lRowF4_of_three (a2lF4Three_holds hC),
      a2lRowE6_of_three (a2lE6Three_holds hC), a2lRowE7_of_three (a2lE7Three_holds hC),
      a2lRowE8_of_three (a2lE8Three_holds hC),
      a2lRowTwistedE6_of_three (a2lTwistedE6Three_of_su6 hC a2lTwistedE6ThreeSU6_holds),
      a2lRowTrialityD4_holds⟩
  exact ⟨⟨tableC_holds, a2l_coverDatum_holds hGr hC,
      a2l_chev3Datum_of_rows hGr hSchur hRows (a2l_chev3Exceptions_holds hGr hCl2),
      twoA7RankOne_holds⟩,
    ⟨⟨ComponentClassification.CatLeafProof.gls3OddLieAutComponentsInput_holds, hCl2, closureSmallCases_holds, a2l_cl4_weak_holds, chevThreeInter_holds⟩,
      residualTwoRank_holds, residualNotChevOdd_holds, twoAnSL25_holds,
      a2l_chev3DatumEnd_of_rows hGr hSchur hO hRows⟩⟩

end CFSG.OddStandard.SmallF3
