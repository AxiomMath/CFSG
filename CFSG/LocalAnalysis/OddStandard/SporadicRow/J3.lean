module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.CompInFiveRow
public import CFSG.HardMathSupport.Foote.FamilyReduction.RowSporadicFour
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Components
public import CFSG.RankThree.PartTwo.Census.Sporadic.J3

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint CFSG.HardMathSupport.Foote.FamilyReduction

theorem sporOddComps_J3
    : SporOddComps .J3 :=
  fun S _ _ _ hna e t ht B hB htB => by
    let φ : S ≃* ↥Sporadic.Schreier.j3P := e.trans Sporadic.Schreier.j3PermEquiv
    have hd := Subgroup.card_subgroup_dvd_card B
    rw [Nat.card_congr (BMCase.gmatCentralizerEquiv φ t).toEquiv,
      RankThree.PartTwo.Census.card_centralizer_j3P (by rw [MulEquiv.orderOf_eq]; exact ht)] at hd
    exact not_oddLieOrder_of_not_compIn5 hna (not_comp5_J3 hna e) ht hB htB (a := 7)
      (hd.trans (by norm_num))

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
