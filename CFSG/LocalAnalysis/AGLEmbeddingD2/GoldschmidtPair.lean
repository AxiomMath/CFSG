module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeV
public import CFSG.Quasithin.Recognition.Gold2Central

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Quasithin CFSG.QuasithinUnique

theorem card_inf_le_two_pow_seven_of_vPair
    {G : Type} [Group G] [Finite G] {I₁ I₂ : Subgroup G} (hp : F6.IsGoldschmidtVPair I₁ I₂) :
    Nat.card ↥(I₁ ⊓ I₂) ≤ 2 ^ 7 := by
  obtain ⟨e₁⟩ := hp.quotient₁
  obtain ⟨e₂⟩ := hp.quotient₂
  by_cases c₁ : CharTwo I₁
  · by_cases c₂ : CharTwo I₂
    · exact F6.card_inf_le_two_pow_seven_of_charTwoLargePair
        F6.GoldAmLarge.goldschmidtCharTwoLargePair_holds hp c₁ c₂
    · exact (gold2_card_inf_le_sixteen_of_not_charTwo_right e₁ e₂ hp.sylow₁ hp.sylow₂
        hp.pCore_eq_bot c₂).trans (by norm_num)
  · exact (gold2_card_inf_le_sixteen_of_not_charTwo_left e₁ e₂ hp.sylow₁ hp.sylow₂
      hp.pCore_eq_bot c₁).trans (by norm_num)

end CFSG.AGLEmbeddingD2
