module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.CompInFiveRow
public import CFSG.HardMathSupport.Foote.FamilyReduction.RowSporadicFour
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Components

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint CFSG.HardMathSupport.Foote.FamilyReduction

theorem sporOddComps_J1
    : SporOddComps .J1 :=
  fun S _ _ _ hna e t ht B hB htB => by
    let φ : S ≃* Open.walterJ1 := e.trans Walter.walterJ1EquivNative.symm
    have hd := Subgroup.card_subgroup_dvd_card B
    rw [Nat.card_congr (BMCase.gmatCentralizerEquiv φ t).toEquiv,
      Walter.J1Props.card_centralizer_of_orderOf_eq_two
        (by rw [MulEquiv.orderOf_eq]; exact ht)] at hd
    exact not_oddLieOrder_of_not_compIn5 hna (not_comp5_J1 e) ht hB htB (a := 3)
      (hd.trans (by norm_num))

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
