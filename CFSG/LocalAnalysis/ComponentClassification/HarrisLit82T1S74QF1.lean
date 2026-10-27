module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74QDefs

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

theorem three_le_card_of_odd_card {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    3 ≤ Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨k, hk⟩ := hodd
  omega

theorem f1Odd_holds : F1Odd := by
  intro K _ _ hodd
  rw [oddCoreOf_eq_radThree hodd (three_le_card_of_odd_card hodd)]
  exact ⟨card_radThree hodd, centralizer_le_sup hodd⟩

end CFSG.ComponentClassification.HarrisLit.T1.S74
