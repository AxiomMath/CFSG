module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.CompInFiveRow
public import CFSG.HardMathSupport.Foote.FamilyReduction.RowSporadicFour
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Components

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint CFSG.HardMathSupport.Foote.FamilyReduction

theorem sporOddComps_M12
    : SporOddComps .M12 :=
  fun S _ _ _ hna e t ht B hB htB => by
    let e' : S ≃* NativeSporadic.M12 := e
    have hd := Subgroup.card_subgroup_dvd_card B
    rw [Nat.card_congr (BMCase.gmatCentralizerEquiv e' t).toEquiv] at hd
    rcases GH74.Generic.S45.LAlt.m12_involution_data (e' t)
        (by rw [MulEquiv.orderOf_eq]; exact ht) with h | ⟨h, -⟩ <;> rw [h] at hd
    · exact not_oddLieOrder_card_quotient_center_of_card_dvd (a := 6) (hd.trans (by norm_num))
    · exact not_oddLieOrder_of_not_compIn5 hna (not_comp5_M12 hna e) ht hB htB (a := 4)
        (hd.trans (by norm_num))

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
