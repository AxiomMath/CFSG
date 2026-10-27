module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ClassicalModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UnitaryTwoLocal
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.LocalAnalysis.RankThreeUC.S15


private lemma rk2Mult_twA_five_le_three {n m : ℕ} (hm : 1 ≤ m) (hm2 : m ≠ 2) :
    rk2Mult (⟨.twA, 5, n⟩ : GLALabel) m ≤ 3 := by
  simp only [rk2Mult]
  norm_num
  split_ifs with h1 h2 h3
  · exact absurd h1 hm2
  · have hm4 : 4 ≤ m := by omega
    rw [Nat.div_le_iff_le_mul (by omega : 0 < m)]
    omega
  · have : 6 / (2 * m) ≤ 6 / 2 := Nat.div_le_div_left (by omega : 2 ≤ 2 * m) (by norm_num)
    omega
  · have hm2' : 2 ≤ m := by omega
    have : 6 / m ≤ 6 / 2 := Nat.div_le_div_left hm2' (by norm_num)
    omega

private lemma rkLin_six_false_three_eq_four {n : ℕ} (ho : Odd n) (h3 : ¬ 3 ∣ n) :
    rkLin 6 false (2 ^ n) 3 1 = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : ((2 : ZMod 3) ^ n) = -1 := by
    have h2eq : (2 : ZMod 3) = -1 := by
      have h31 : (2 : ZMod 3) + 1 = 0 := by
        rw [show (2 : ZMod 3) + 1 = ((3 : ℕ) : ZMod 3) by norm_num]
        exact ZMod.natCast_self 3
      exact (eq_neg_iff_add_eq_zero).mpr h31
    rw [h2eq, Odd.neg_one_pow ho]
  have hqcast : ((2 ^ n : ℕ) : ZMod 3) = -1 := by
    push_cast
    exact hq
  have hem : eM (2 ^ n) 3 = 1 := by
    simp only [eM, hqcast]
    norm_num
  have hv3 : padicValNat 3 (2 ^ n + 1) = 1 := by
    have hmain := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
      (by decide : Odd 3) (by norm_num : 3 ∣ 2 + 1) (by norm_num : ¬ 3 ∣ 2) ho
    rw [one_pow] at hmain
    have h31 : padicValNat 3 (2 + 1) = 1 := by norm_num [padicValNat]
    have h3n : padicValNat 3 n = 0 := padicValNat.eq_zero_of_not_dvd h3
    rw [h31, h3n, add_zero] at hmain
    exact hmain
  have h36 : padicValNat 3 6 = 1 := by
    have h1 : 1 ≤ padicValNat 3 6 := one_le_padicValNat_of_dvd (by norm_num) (by norm_num)
    have h2 : ¬ (2 ≤ padicValNat 3 6) := by
      intro hh
      have h9 : 3 ^ 2 ∣ 6 :=
        (padicValNat_dvd_iff_le (p := 3) (a := 6) (by norm_num : (6 : ℕ) ≠ 0)).mpr hh
      norm_num at h9
    omega
  have hcond : ¬ 3 ∣ 1 ∧ 3 ∣ 6 ∧ 4 ≤ 6 ∧ padicValNat 3 (2 ^ n + 1) ≤ padicValNat 3 6 := by
    refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hv3, h36]
  unfold rkLin
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos hem, if_pos hcond]

theorem rk2_pRank_twa5_le_three (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab) (ht : lab.tag = .twA ∧ lab.rank = 5)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : ¬ p ∣ 2 ^ lab.n + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 3 := by
  obtain ⟨t, l, n⟩ := lab
  simp only at ht hq ⊢
  obtain ⟨rfl, rfl⟩ := ht
  have hmain : CFSG.Open.pRank p (⊤ : Subgroup K) ≤
      rk2Mult (⟨.twA, 5, n⟩ : GLALabel) (rk2Ord p n) :=
    rk2KRank_classical hG hK hp hp2 (by simp)
  refine hmain.trans ?_
  exact rk2Mult_twA_five_le_three (rk2Ord_pos hp hp2 n)
    fun h2 => hq ((rk2Ord_eq_two_iff hp hp2).mp h2)

theorem rk2_pRank_twa5_eq_four_of_three (hG : CFSG.Open.GriessAllModelsStatement) {K : Type}
    [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (ht : lab.tag = .twA ∧ lab.rank = 5) (hc : Subgroup.center K = ⊥)
    (h3 : ¬ (3 ∣ lab.n ∧ Odd lab.n)) (hdvd : 3 ∣ 2 ^ lab.n + 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 4 := by
  obtain ⟨t, l, n⟩ := lab
  simp only at ht h3 hdvd ⊢
  obtain ⟨rfl, rfl⟩ := ht
  have hC : LieOddRankChev := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev hG
  have hexact : CFSG.Open.pRank 3 (⊤ : Subgroup K) =
      rk2Chev (⟨.twA, 5, n⟩ : GLALabel) 3 (Nat.card (Subgroup.center K)) :=
    rk2_pRank_eq_of_isLabel_classical hC hK Nat.prime_three (by norm_num)
      (by simp) (fun h => absurd h (by simp)) (fun h => absurd h (by simp))
      (fun h => absurd h (by simp)) (fun h => absurd h (by simp))
      (fun h => absurd h (by simp))
  rw [hexact]
  have hcard : Nat.card (Subgroup.center K) = 1 := by rw [hc, Subgroup.card_bot]
  have hchev : rk2Chev (⟨.twA, 5, n⟩ : GLALabel) 3 (Nat.card (Subgroup.center K)) =
      rkLin 6 false (2 ^ n) 3 1 := by
    simp [rk2Chev, hcard]
  rw [hchev]
  have hnodd : Odd n := by
    rcases Nat.even_or_odd n with he | ho
    · exfalso
      obtain ⟨k, hk⟩ := he
      have h2 : n = 2 * k := by omega
      rw [h2] at hdvd
      have h4 : ((2 : ZMod 3) ^ (2 * k)) = 1 := by
        rw [pow_mul]
        have h22 : ((2 : ZMod 3) ^ 2) = 1 := by
          have h31 : (2 : ZMod 3) + 1 = 0 := by
            rw [show (2 : ZMod 3) + 1 = ((3 : ℕ) : ZMod 3) by norm_num]
            exact ZMod.natCast_self 3
          have h2eq : (2 : ZMod 3) = -1 := (eq_neg_iff_add_eq_zero).mpr h31
          rw [h2eq]
          ring
        rw [h22, one_pow]
      have h0 : ((2 ^ (2 * k) + 1 : ℕ) : ZMod 3) = 0 :=
        (ZMod.natCast_eq_zero_iff (2 ^ (2 * k) + 1) 3).mpr hdvd
      push_cast at h0
      rw [h4] at h0
      exact absurd ((ZMod.natCast_eq_zero_iff 2 3).mp h0) (by norm_num)
    · exact ho
  have hn3 : ¬ 3 ∣ n := fun h => h3 ⟨h, hnodd⟩
  rw [rkLin_six_false_three_eq_four hnodd hn3]

private lemma nine_dvd_two_pow_add_one_of_odd {n : ℕ} (h3 : 3 ∣ n) (ho : Odd n) : 9 ∣ 2 ^ n + 1 := by
  have hmain := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
    (by decide : Odd 3) (by norm_num : 3 ∣ 2 + 1) (by norm_num : ¬ 3 ∣ 2) ho
  rw [one_pow] at hmain
  have h31 : padicValNat 3 (2 + 1) = 1 := by norm_num [padicValNat]
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at ho
  have h3n : 1 ≤ padicValNat 3 n := one_le_padicValNat_of_dvd hn0 h3
  rw [h31] at hmain
  have h2 : 2 ≤ padicValNat 3 (2 ^ n + 1) := by omega
  have h9 : 3 ^ 2 ∣ 2 ^ n + 1 :=
    (padicValNat_dvd_iff_le (p := 3) (a := 2 ^ n + 1) (by positivity)).mpr h2
  simpa using h9

theorem rk2_up_twa5 {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (ht : lab.tag = .twA ∧ lab.rank = 5) (hn : 2 ≤ lab.n) (hc : Subgroup.center K = ⊥)
    (hG : CFSG.Open.GriessAllModelsStatement)
    (h3sq : 9 ∣ 2 ^ lab.n + 1 → CFSG.Open.twoLocalPrimeRank 3 K ≤ 4) :
    evenRank K ≤ 4 := by
  rw [CFSG.RankThreeEvenClassification.Helpers.evenRank_eq_sup_twoLocalRanks]
  refine csSup_le' ?_
  rintro k ⟨p, hp, hp2, rfl⟩
  by_cases hq : p ∣ 2 ^ lab.n + 1
  · by_cases hp3 : p = 3
    ·
      subst hp3
      by_cases h9 : 9 ∣ 2 ^ lab.n + 1
      · exact h3sq h9
      ·
        have h3 : ¬ (3 ∣ lab.n ∧ Odd lab.n) := by
          rintro ⟨h3n, hodd⟩
          exact h9 (nine_dvd_two_pow_add_one_of_odd h3n hodd)
        exact (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank 3
          Nat.prime_three K).trans
          (rk2_pRank_twa5_eq_four_of_three hG hK ht hc h3 hq)
    ·
      obtain ⟨-, hlab, hM⟩ := rk2_model_of_isLabel hK
      have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 6 2 lab.n := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
          CFSG.StandardType.markRank, CFSG.StandardType.markChar,
          CFSG.StandardType.markDeg, ht.1, ht.2] using hM
      obtain ⟨-, F, hF, hFin, hFcard, ⟨φ⟩⟩ :=
        hM'.statedClassicalModel (by decide : StatedLieTag.PSU ∈ classicalTags)
      letI : Field F := hF
      letI : Finite F := hFin
      haveI : CharP F 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (k := 2 * lab.n) (by omega)
          (by rw [hFcard, show 2 * lab.n = lab.n * 2 by omega, ← pow_mul])
      let eZ : K ⧸ Subgroup.center K ≃* K :=
        (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
      let eK : K ≃* StatedProj (StatedSU 6 (2 ^ lab.n) F) := eZ.symm.trans φ
      have he : GLATwoLocalRank p (StatedProj (StatedSU 6 (2 ^ lab.n) F)) =
          GLATwoLocalRank p K :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr hp.one_lt eK
      change GLATwoLocalRank p K ≤ 4
      rw [← he]
      exact CFSG.RankThree.PartOne.KFU.twoLocalPrimeRank_statedProj_statedSU_six_le_four_of_ne_three
        hFcard hp hp2 hp3 hq
  ·
    exact (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp K).trans
      (le_trans (rk2_pRank_twa5_le_three hG hK ht hp hp2 hq) (by norm_num))

end CFSG.LocalAnalysis.GLTheoremA
