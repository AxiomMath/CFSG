module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcFive

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LieType.SeitzGeneration

@[expose] def CrossE7SevenSplit : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid),
    (7 ∣ q.card - 1 ∨ 7 ∣ q.card + 1) → CrossAtPrime ⟨.E7 q, hv⟩ 7

@[expose] def CrossE8FiveFour : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid),
    orderOf ((q.card : ℕ) : ZMod 5) = 4 → CrossAtPrime ⟨.E8 q, hv⟩ 5

section Catalog


theorem crossFamE7Small_of_split (h : CrossE7SevenSplit) : CrossFamE7Small := fun q hv => by
  refine ⟨crossAtPrime_E7_five hv, fun hp hp5 hdp => ?_⟩
  have hpq : (7 : ℕ) ≠ q.p := fun h' => hdp (by
    rw [TauCeti.LieTypeIndex.characteristic_E7]; exact h'.symm)
  rcases dvd_sub_one_or_dvd_add_one_or_three_le hp (not_dvd_card_of_ne hp hpq) with h1 | h2 | h3
  · exact h q hv (Or.inl h1) hp hp5 hdp
  · exact h q hv (Or.inr h2) hp hp5 hdp
  · exact crossAtPrime_E7_seven_of_three_le hv h3 hp hp5 hdp

theorem crossFamE8Small_of_four (h : CrossE8FiveFour) : CrossFamE8Small := fun q hv => by
  refine ⟨fun hp hp5 hdp => ?_, crossAtPrime_E8_seven hv⟩
  have hpq : (5 : ℕ) ≠ q.p := fun h' => hdp (by
    rw [TauCeti.LieTypeIndex.characteristic_E8]; exact h'.symm)
  have hnd : ¬ 5 ∣ q.card := not_dvd_card_of_ne hp hpq
  have hq1 : 1 ≤ q.card := Nat.pos_of_ne_zero fun h0 => hnd (h0 ▸ dvd_zero 5)
  rcases orderOf_five_eq hnd with h1 | h2 | h4
  · exact crossAtPrime_E8_of_dvd hv (by norm_num) (dvd_sub_one_of_orderOf_eq_one hp hq1 h1) hp
      hp5 hdp
  · exact crossAtPrime_E8_of_dvd_add_one hv (by norm_num) (dvd_add_one_of_orderOf_eq_two hp h2)
      hp hp5 hdp
  · exact h q hv h4 hp hp5 hdp

end Catalog

end CFSG.LocalAnalysis.RankFourTheoremC
