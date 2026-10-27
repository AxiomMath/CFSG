module

public import CFSG.LocalAnalysis.OddStandard.SporadicRow.CompInFiveRow
public import CFSG.HardMathSupport.Foote.FamilyReduction.RowSporadicFour
public import CFSG.GH74.Generic.S45.LSporJ2
public import CFSG.LocalAnalysis.OddStandard.SporadicRow.Components

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint CFSG.HardMathSupport.Foote.FamilyReduction

theorem sporOddComps_J2
    : SporOddComps .J2 :=
  fun S _ _ _ hna e t ht B hB htB => by
    let φ : S ≃* J2Cover.P := e.trans J2Cover.nativeEquivP
    have hd := Subgroup.card_subgroup_dvd_card B
    rw [Nat.card_congr (BMCase.gmatCentralizerEquiv φ t).toEquiv] at hd
    have hd' : Nat.card ↥B ∣ 2 ^ 7 * 15 := by
      rcases GH74.Generic.S45.j2_involution_data (p := φ t)
          (by rw [MulEquiv.orderOf_eq]; exact ht) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hd <;>
        exact hd.trans (by norm_num)
    exact not_oddLieOrder_of_not_compIn5 hna (not_comp5_J2 hna e) ht hB htB hd'

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
