module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCasesLin
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCasesOther

public section

namespace CFSG.LocalAnalysis.AGL81I.Section4

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeUC.S15

private theorem not_dvd_card {Q : TauCeti.PrimePower} {p : ℕ} (hQ : Q.p = 2) (hp : p.Prime)
    (hp5 : 5 ≤ p) : ¬ p ∣ Q.card := by
  have hp2 : p ≠ 2 := by omega
  rw [TauCeti.PrimePower.card_def, hQ]
  exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem three_le_eP {Q p : ℕ} (hp : p.Prime) (hQ : 1 ≤ Q) (hpQ : ¬ p ∣ Q)
    (h : ¬ p ∣ Q ^ 2 - 1) : 3 ≤ eP Q p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < eP Q p := by
    rw [eP, orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
    have hQ0 : (Q : ZMod p) ≠ 0 := fun h0 =>
      hpQ ((CharP.cast_eq_zero_iff (ZMod p) p Q).1 h0)
    have h := FiniteField.pow_card_sub_one_eq_one (Q : ZMod p) hQ0
    rw [ZMod.card] at h
    exact h
  rcases Nat.lt_or_ge (eP Q p) 3 with hlt | hge
  · have h12 : eP Q p = 1 ∨ eP Q p = 2 := by omega
    rcases h12 with h1 | h2
    · exact absurd (((eP_eq_one_iff hQ).1 h1).trans (by
        simpa using Nat.sub_dvd_pow_sub_pow Q 1 2)) h
    · exact absurd ((eS_eq_one_iff hQ).1 (by rw [eS_eq_eP_div_gcd, h2]; norm_num)) h
  · exact hge

theorem three_le_eM {Q p : ℕ} (hp : p.Prime) (hQ : 1 ≤ Q) (hpQ : ¬ p ∣ Q)
    (h : ¬ p ∣ Q ^ 2 - 1) : 3 ≤ eM Q p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < eM Q p := by
    rw [eM, orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    refine ⟨p - 1, by have := hp.two_le; omega, ?_⟩
    have hQ0 : (-(Q : ZMod p)) ≠ 0 := fun h0 => hpQ
      ((CharP.cast_eq_zero_iff (ZMod p) p Q).1 (neg_eq_zero.mp h0))
    have h := FiniteField.pow_card_sub_one_eq_one (-(Q : ZMod p)) hQ0
    rw [ZMod.card] at h
    exact h
  rcases Nat.lt_or_ge (eM Q p) 3 with hlt | hge
  · have h12 : eM Q p = 1 ∨ eM Q p = 2 := by omega
    rcases h12 with h1 | h2
    · refine absurd (((eM_eq_one_iff).1 h1).trans ?_) h
      have : Q + 1 ∣ Q ^ 2 - 1 := by
        have h := Nat.sq_sub_sq Q 1
        rw [show Q ^ 2 - 1 = (Q + 1) * (Q - 1) by simpa using h]
        exact dvd_mul_right _ _
      exact this
    · exact absurd ((eS_eq_one_iff hQ).1 (by
        unfold eS
        have hsq : (-(Q : ZMod p)) ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
        rw [show (Q : ZMod p) ^ 2 = (-(Q : ZMod p)) ^ 2 by
          rw [pow_two, pow_two]
          exact (neg_mul_neg _ _).symm, hsq, orderOf_one])) h
  · exact hge

theorem two_le_eS {Q p : ℕ} (hp : p.Prime) (hQ : 1 ≤ Q) (hpQ : ¬ p ∣ Q)
    (h : ¬ p ∣ Q ^ 2 - 1) : 2 ≤ eS Q p := by
  have h3 := three_le_eP hp hQ hpQ h
  rw [eS_eq_eP_div_gcd]
  have hg : Nat.gcd (eP Q p) 2 ≤ 2 := Nat.gcd_le_right _ (by norm_num)
  have hgpos : 0 < Nat.gcd (eP Q p) 2 := Nat.gcd_pos_of_pos_left 2 (by omega)
  rcases (show Nat.gcd (eP Q p) 2 = 1 ∨ Nat.gcd (eP Q p) 2 = 2 by omega) with hg1 | hg2
  · rw [hg1, Nat.div_one]
    omega
  · rw [hg2]
    have hdvd : 2 ∣ eP Q p := by
      have := Nat.gcd_dvd_left (eP Q p) 2
      rwa [hg2] at this
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_div_right k (by norm_num)]
    omega

theorem rkLin_le_div {m Q p z : ℕ} {eps : Bool}
    (h : 3 ≤ (if eps then eP Q p else eM Q p)) : rkLin m eps Q p z ≤ m / 3 := by
  unfold rkLin
  have h1 : (if eps then eP Q p else eM Q p) ≠ 1 := by omega
  rw [if_neg h1]
  exact Nat.div_le_div_left h (by norm_num)

theorem rkSp_le_div {l Q p : ℕ} (h : 2 ≤ eS Q p) : rkSp l Q p ≤ l / 2 := by
  unfold rkSp
  exact Nat.div_le_div_left h (by norm_num)

theorem rkOmMinus_le_div {l Q p : ℕ} (h : 2 ≤ eS Q p) : rkOmMinus l Q p ≤ l / 2 := by
  unfold rkOmMinus
  have h1 : l / eS Q p ≤ l / 2 := Nat.div_le_div_left (a := l) h (by norm_num)
  omega

theorem rkG2_le_one {Q p : ℕ} (h : 2 ≤ eS Q p) : rkG2 Q p ≤ 1 := by
  unfold rkG2
  split_ifs <;> omega

theorem mRankChev_A_le {l : ℕ} {Q : TauCeti.PrimePower} {z p : ℕ} (hQ : Q.p = 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hnot : ¬ p ∣ Q.card ^ 2 - 1)
    (h3 : mRankChev (.A l Q) 3 z ≤ 3) (hl : 1 ≤ l) :
    mRankChev (.A l Q) p z + 1 ≤ max 2 (mRankChev (.A l Q) 3 z) := by
  have hQ1 : 1 ≤ Q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ (by have := Q.prime_p.two_le; omega)
  have hpQ := not_dvd_card hQ hp hp5
  have heP3 : 3 ≤ eP Q.card p := three_le_eP hp hQ1 hpQ hnot
  have hcard : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have heP : eP Q.card 3 = if Even Q.exponent then 1 else 2 := by
    rw [hcard]; exact eP_two_pow_three _
  change rkLin (l + 1) true Q.card p z + 1 ≤ max 2 (rkLin (l + 1) true Q.card 3 z)
  have hb : rkLin (l + 1) true Q.card p z ≤ (l + 1) / 3 := rkLin_le_div heP3
  by_cases hEven : Even Q.exponent
  · have he1 : eP Q.card 3 = 1 := by rw [heP, if_pos hEven]
    obtain ⟨δ, hδ, -, hB⟩ := rk3Cases_A_aux_rkLin_one (l + 1) true Q.card z he1
    set A := rkLin (l + 1) true Q.card p z
    set B := rkLin (l + 1) true Q.card 3 z
    have hA : A ≤ (l + 1) / 3 := hb
    have h3B : B ≤ 3 := h3
    have hBeq : B = l + 1 - 1 - δ := hB
    have hm : l ≤ 4 := by omega
    interval_cases l <;> norm_num at hA h3B hBeq ⊢ <;> omega
  · have he2 : eP Q.card 3 = 2 := by rw [heP, if_neg hEven]
    have hB := rk3Cases_A_aux_rkLin_two (l + 1) true Q.card z he2
    set A := rkLin (l + 1) true Q.card p z
    set B := rkLin (l + 1) true Q.card 3 z
    have hA : A ≤ (l + 1) / 3 := hb
    have h3B : B ≤ 3 := h3
    have hBeq : B = (l + 1) / 2 := hB
    have hm : l ≤ 6 := by
      by_contra h
      have h8 : 8 ≤ l + 1 := by omega
      have h4 : 4 ≤ (l + 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
      omega
    interval_cases l <;> norm_num at hA h3B hBeq ⊢ <;> omega

theorem mRankChev_tA_le {l : ℕ} {Q : TauCeti.PrimePower} {z p : ℕ} (hQ : Q.p = 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hnot : ¬ p ∣ Q.card ^ 2 - 1)
    (h3 : mRankChev (.twistedA l Q) 3 z ≤ 3) (hl : 2 ≤ l) :
    mRankChev (.twistedA l Q) p z + 1 ≤ max 2 (mRankChev (.twistedA l Q) 3 z) := by
  have hQ1 : 1 ≤ Q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ (by have := Q.prime_p.two_le; omega)
  have hpQ := not_dvd_card hQ hp hp5
  have heM3 : 3 ≤ eM Q.card p := three_le_eM hp hQ1 hpQ hnot
  have hcard : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have heM : eM Q.card 3 = if Even Q.exponent then 2 else 1 := by
    rw [hcard]; exact eM_two_pow_three _
  change rkLin (l + 1) false Q.card p z + 1 ≤ max 2 (rkLin (l + 1) false Q.card 3 z)
  have hb : rkLin (l + 1) false Q.card p z ≤ (l + 1) / 3 := rkLin_le_div heM3
  by_cases hEven : Even Q.exponent
  · have he2 : eM Q.card 3 = 2 := by rw [heM, if_pos hEven]
    have hB := rk3Cases_A_aux_rkLin_two (l + 1) false Q.card z he2
    set A := rkLin (l + 1) false Q.card p z
    set B := rkLin (l + 1) false Q.card 3 z
    have hA : A ≤ (l + 1) / 3 := hb
    have h3B : B ≤ 3 := h3
    have hBeq : B = (l + 1) / 2 := hB
    have hm : l ≤ 6 := by
      by_contra h
      have h8 : 8 ≤ l + 1 := by omega
      have h4 : 4 ≤ (l + 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
      omega
    interval_cases l <;> norm_num at hA h3B hBeq ⊢ <;> omega
  · have he1 : eM Q.card 3 = 1 := by rw [heM, if_neg hEven]
    obtain ⟨δ, hδ, -, hB⟩ := rk3Cases_A_aux_rkLin_one (l + 1) false Q.card z he1
    set A := rkLin (l + 1) false Q.card p z
    set B := rkLin (l + 1) false Q.card 3 z
    have hA : A ≤ (l + 1) / 3 := hb
    have h3B : B ≤ 3 := h3
    have hBeq : B = l + 1 - 1 - δ := hB
    have hm : l ≤ 4 := by omega
    interval_cases l <;> norm_num at hA h3B hBeq ⊢ <;> omega

theorem mRankChev_B_le {l : ℕ} {Q : TauCeti.PrimePower} {z p : ℕ} (hQ : Q.p = 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hnot : ¬ p ∣ Q.card ^ 2 - 1)
    (h3 : mRankChev (.B l Q) 3 z ≤ 3) (hl : 2 ≤ l) :
    mRankChev (.B l Q) p z + 1 ≤ max 2 (mRankChev (.B l Q) 3 z) := by
  have hQ1 : 1 ≤ Q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ (by have := Q.prime_p.two_le; omega)
  have hpQ := not_dvd_card hQ hp hp5
  have heS2 : 2 ≤ eS Q.card p := two_le_eS hp hQ1 hpQ hnot
  have hB : rkSp l Q.card 3 = l := rk3CasesOther_mRank_B hQ z
  have hb : rkSp l Q.card p ≤ l / 2 := rkSp_le_div heS2
  have h3B : rkSp l Q.card 3 ≤ 3 := h3
  change rkSp l Q.card p + 1 ≤ max 2 (rkSp l Q.card 3)
  rw [hB] at h3B ⊢
  interval_cases l <;> norm_num at hb ⊢ <;> omega

theorem mRankChev_D_le {l : ℕ} {Q : TauCeti.PrimePower} {z p : ℕ} (hQ : Q.p = 2)
    (h3 : mRankChev (.D l Q) 3 z ≤ 3) (hl : 4 ≤ l) :
    mRankChev (.D l Q) p z + 1 ≤ max 2 (mRankChev (.D l Q) 3 z) := by
  change rkOmPlus l Q.card p + 1 ≤ max 2 (rkOmPlus l Q.card 3)
  have h3' : rkOmPlus l Q.card 3 ≤ 3 := h3
  have h4 : 4 ≤ rkOmPlus l Q.card 3 := rk3CasesOther_mRank_D hQ hl z
  omega

theorem mRankChev_tD_le {l : ℕ} {Q : TauCeti.PrimePower} {z p : ℕ} (hQ : Q.p = 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hnot : ¬ p ∣ Q.card ^ 2 - 1)
    (h3 : mRankChev (.twistedD l Q) 3 z ≤ 3) (hl : 4 ≤ l) :
    mRankChev (.twistedD l Q) p z + 1 ≤ max 2 (mRankChev (.twistedD l Q) 3 z) := by
  have hQ1 : 1 ≤ Q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ (by have := Q.prime_p.two_le; omega)
  have hpQ := not_dvd_card hQ hp hp5
  have heS2 : 2 ≤ eS Q.card p := two_le_eS hp hQ1 hpQ hnot
  have hb : rkOmMinus l Q.card p ≤ l / 2 := rkOmMinus_le_div heS2
  change rkOmMinus l Q.card p + 1 ≤ max 2 (rkOmMinus l Q.card 3)
  set A := rkOmMinus l Q.card p
  set B := rkOmMinus l Q.card 3
  set e := if eP Q.card 3 ∣ l then 1 else 0 with he
  have hB : B = l - e := rk3CasesOther_mRank_tD hQ z
  have h3B : B ≤ 3 := h3
  have he0 : e ≤ 1 := by rw [he]; split_ifs <;> norm_num
  have hA : A ≤ l / 2 := hb
  have hl4 : l = 4 := by omega
  subst hl4
  norm_num at hA hB ⊢
  omega

theorem mRankChev_G2_le {Q : TauCeti.PrimePower} {z p : ℕ} (hQ : Q.p = 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hnot : ¬ p ∣ Q.card ^ 2 - 1)
    (h3 : mRankChev (.G2 Q) 3 z ≤ 3) :
    mRankChev (.G2 Q) p z + 1 ≤ max 2 (mRankChev (.G2 Q) 3 z) := by
  have hQ1 : 1 ≤ Q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ (by have := Q.prime_p.two_le; omega)
  have hpQ := not_dvd_card hQ hp hp5
  have heS2 : 2 ≤ eS Q.card p := two_le_eS hp hQ1 hpQ hnot
  have hb : rkG2 Q.card p ≤ 1 := rkG2_le_one heS2
  have hB : rkG2 Q.card 3 = 2 := rk3CasesOther_mRank_G2 hQ z
  have h3B : rkG2 Q.card 3 ≤ 3 := h3
  change rkG2 Q.card p + 1 ≤ max 2 (rkG2 Q.card 3)
  rw [hB] at h3B ⊢
  norm_num at hb ⊢
  omega

theorem mRankChev_add_one_le {d : TauCeti.LieTypeIndex} {z p : ℕ} (hv : d.Valid)
    (hd : IsClassicalOrG2Index d) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hnot : ¬ p ∣ d.fieldOrder ^ 2 - 1) (h3 : mRankChev d 3 z ≤ 3) :
    mRankChev d p z + 1 ≤ max 2 (mRankChev d 3 z) := by
  have hrange := ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
  cases d
  case A l Q =>
    simp only [IsClassicalOrG2Index] at hd
    simp only [TauCeti.LieTypeIndex.fieldOrder_A] at hnot
    have hl : 1 ≤ l := ((TauCeti.LieTypeIndex.inStandardRange_iff (.A l Q)).1 hrange).1
    exact mRankChev_A_le hd hp hp5 hnot h3 hl
  case twistedA l Q =>
    simp only [IsClassicalOrG2Index] at hd
    simp only [TauCeti.LieTypeIndex.fieldOrder_twistedA] at hnot
    have hl : 2 ≤ l := ((TauCeti.LieTypeIndex.inStandardRange_iff (.twistedA l Q)).1 hrange).1
    exact mRankChev_tA_le hd hp hp5 hnot h3 hl
  case B l Q =>
    simp only [IsClassicalOrG2Index] at hd
    simp only [TauCeti.LieTypeIndex.fieldOrder_B] at hnot
    have hl : 2 ≤ l := ((TauCeti.LieTypeIndex.inStandardRange_iff (.B l Q)).1 hrange).1
    exact mRankChev_B_le hd hp hp5 hnot h3 hl
  case D l Q =>
    simp only [IsClassicalOrG2Index] at hd
    have hl : 4 ≤ l := (TauCeti.LieTypeIndex.inStandardRange_iff (.D l Q)).1 hrange
    exact mRankChev_D_le hd h3 hl
  case twistedD l Q =>
    simp only [IsClassicalOrG2Index] at hd
    simp only [TauCeti.LieTypeIndex.fieldOrder_twistedD] at hnot
    have hl : 4 ≤ l := (TauCeti.LieTypeIndex.inStandardRange_iff (.twistedD l Q)).1 hrange
    exact mRankChev_tD_le hd hp hp5 hnot h3 hl
  case G2 Q =>
    simp only [IsClassicalOrG2Index] at hd
    simp only [TauCeti.LieTypeIndex.fieldOrder_G2] at hnot
    exact mRankChev_G2_le hd hp hp5 hnot h3
  case C | suzuki | reeG2 | reeF4 | E6 | E7 | E8 | F4 | twistedE6 | trialityD4 | tits =>
    simp only [IsClassicalOrG2Index] at hd

end CFSG.LocalAnalysis.AGL81I.Section4

end
