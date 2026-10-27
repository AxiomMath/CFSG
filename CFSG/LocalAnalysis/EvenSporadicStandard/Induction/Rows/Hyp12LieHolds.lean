module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Hyp12LieCat
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Hyp12LieFi23
import CFSG.LocalAnalysis.SeitzReduction.GLS3OddHolds
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOuter
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSROrd
import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableCo
import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableFi
import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableMonster

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp12Lie

set_option linter.unusedSectionVars false

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatFC

section Fi23

theorem fi23NoTightU62_holds : Fi23NoTightU62 := by
  intro S _ e L hq hcard htight z hz hzL
  exact fi23_false_of_tight_u62 e hq hcard htight hz hzL

end Fi23

section Cat

theorem sol78Hyp12LieCat_holds : Sol78Hyp12LieCat :=
  sol78Hyp12LieCat_of_inputs CFSG.SeitzReduction.gls3OddLieAutComponentsInput
    (fun T _ hT u hu B => involutionCentralizersComponentFree_of_evenLieType hT u hu B)
    CFSG.ComponentClassification.CatLeafProof.evenLieOuterTwoComponentsInput_holds
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.ComponentClassification.GSThmB.QPUSpor.card_carrier_eq_sporOrder
    sporadic_rows_co1 sporadic_rows_co2 sporadic_rows_fi24 sporadic_rows_b sporadic_rows_m
    fi23NoTightU62_holds

end Cat

end CFSG.EvenSporadicStandard.Induction.Hyp12Lie
