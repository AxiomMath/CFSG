module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitUntwisted
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwistedA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwistedDPlus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwistedE6Five
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviBound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UnitaryCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UnitaryTwoLocalProj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem twoLocalPrimeRank_statedSU_quot_le_of_dvd (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f d : ℕ),
      Nat.card F = (2 ^ f) ^ 2 → 3 ≤ d → r ∣ 2 ^ f + 1 →
        ∀ (C : Subgroup (StatedSU d (2 ^ f) F)) [C.Normal],
          C ≤ Subgroup.center (StatedSU d (2 ^ f) F) →
            CFSG.Open.twoLocalPrimeRank r (StatedSU d (2 ^ f) F ⧸ C) ≤ d - 2 := by
  intro F _ _ _ f d hK hd hrq C hCn hC
  haveI : C.Normal := hCn
  refine twoLocalPrimeRank_statedSU_quot_le hK hd hr hr2 hrq C hC ?_
  intro V _ _ _ R hR hcomm hpow
  exact CFSG.GroupTheory.card_le_pow_finrank_sub_one_mul_card_scalar hr hr2 (by
    rw [hK]
    exact hrq.trans (CFSG.LieType.SeitzGeneration.dvd_sq_sub_one_of_dvd_add_one
      (p := 2 ^ f + 1) (q := 2 ^ f) dvd_rfl)) R hR hcomm hpow


theorem rk2SplitInputs_holds : Rk2SplitInputs := by
  refine
    { w1_A := ?_
      w1_BCD := ?_
      w1_E6 := ?_
      w1_E7 := ?_
      w1_E8 := ?_
      w2_twA := ?_
      h_twA := ?_
      w3_twD := ?_
      w4_twE6_lower := ?_
      w4_twE6_upper := ?_
      w4_twE6_five := ?_
      w5_A := ?_
      w5_BCD := ?_
      w5_E7 := ?_
      w5_E8 := ?_ }
  · intro K _ _ lab p hK htag hp hp2 hpq
    exact rk2_split_low_A hK hp hp2 htag hpq
  · intro K _ _ lab p hK htag hp hp2 hpq
    exact rk2_split_low_BCD hK hp hp2 htag hpq
  · intro K _ _ lab p hK htag hp hp2 hpq
    exact rk2_split_low_E6 hK hp hp2 htag hpq
  · intro K _ _ lab p hK htag hp hp2 hpq
    exact rk2_split_low_E7 hK hp hp2 htag hpq
  · intro K _ _ lab p hK htag hp hp2 hpq
    exact rk2_split_low_E8 hK hp hp2 htag hpq
  · intro K _ _ lab p hK htag hp hp2 hpq
    exact rk2_split_low_twA hK hp hp2 htag hpq
  · intro K _ _ lab r hK htag hn hr hr2 hrq
    exact rk2_split_up_twA CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      hK htag hn hr hr2 hrq (twoLocalPrimeRank_statedSU_quot_le_of_dvd r hr hr2)
  · intro K _ _ lab p hK htag h4 hp hp2 hpq
    exact rk2_split_low_twD hK hp hp2 htag h4 hpq
  · intro K _ _ lab p hK htag hn hp hp2 hpq
    exact rk2_split_low_twE6 hK hp hp2 htag hn hpq
  · intro K _ _ lab r hK htag hn hr hr5 hrq
    exact rk2_split_up_twE6 rk2TwE6LeviRankInputMaximal_holds hK htag hn hr hr5 hrq
  · intro K _ _ lab p hK htag hn hp hp5 hpq
    exact rk2_split_low_twE6_five hK htag hn hp hp5 hpq
  · intro K _ _ lab p hK htag hn hp3
    rw [hp3]
    exact rk2_split_low_A_one hK htag hn
  · intro K _ _ lab p hK htag hn hp3
    rw [hp3]
    exact rk2_split_low_BCD_one hK htag hn
  · intro K _ _ lab p hK htag hn hp3
    rw [hp3]
    exact rk2_split_low_E7_one hK htag hn
  · intro K _ _ lab p hK htag hn hp3
    rw [hp3]
    exact rk2_split_low_E8_one hK htag hn

theorem rk2Split_holds : Rk2Split :=
  rk2Split_of_inputs rk2SplitInputs_holds

end CFSG.LocalAnalysis.GLTheoremA
