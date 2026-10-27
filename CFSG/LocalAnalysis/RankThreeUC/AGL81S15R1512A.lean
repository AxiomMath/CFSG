module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankNT3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankEq2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem rank_ge_four_aux {m : ℕ} (hm5 : 5 ≤ m) (hm7 : m ≤ 7) {Q : TauCeti.PrimePower}
    (hQ : Q.p = 2) (hn2 : 2 ≤ Q.exponent) {z : ℕ} {eps : Bool}
    (heps : eps = decide (Odd Q.exponent))
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → rkLin m eps Q.card r z ≤ 3) :
    m = 5 ∧ Q.exponent = 2 ∧ ¬ 5 ∣ z := by
  rcases exists_prime_rank_ge_four Q.exponent m z hn2 hm5 hm7 with ⟨h1, h2, h3⟩ | ⟨q, hq, hqd, hge⟩
  · exact ⟨h1, h2, h3⟩
  · exfalso
    have hq2 : q ≠ 2 := by
      rintro rfl
      have h2n : 2 ∣ 2 ^ Q.exponent := dvd_pow_self 2 (by omega)
      have hpos : 0 < 2 ^ Q.exponent := by positivity
      obtain ⟨k, hk⟩ := h2n
      split_ifs at hqd
      · obtain ⟨j, hj⟩ := hqd
        omega
      · obtain ⟨j, hj⟩ := hqd
        omega
    have h' := h q hq hq2
    rw [TauCeti.PrimePower.card_def, hQ, heps] at h'
    omega

@[expose] def Res1512 : TauCeti.LieTypeIndex → Prop
  | .A l Q => 4 ≤ l ∧ l ≤ 6 ∧ Q.p = 2 ∧ Odd Q.exponent ∧ 3 ≤ Q.exponent
  | .twistedA l Q => 4 ≤ l ∧ l ≤ 6 ∧ Q.p = 2 ∧ Even Q.exponent ∧ (l = 4 → 4 ≤ Q.exponent)
  | _ => False

theorem isRankTwoPlus_of_res1512 {d : TauCeti.LieTypeIndex} (hd : Res1512 d) :
    IsRankTwoPlus d := by
  cases d with
  | A l Q =>
    obtain ⟨h4, h6, hQ, -⟩ := hd
    exact ⟨hQ, by omega⟩
  | twistedA l Q =>
    obtain ⟨h4, h6, hQ, -⟩ := hd
    exact ⟨hQ, by omega⟩
  | _ => exact hd.elim

theorem in1512_or_res1512 {d : TauCeti.LieTypeIndex} (hd : IsRankTwoPlus d) {z : ℕ}
    (h3 : mRankChev d 3 z ≤ 3) : In1512 d ∨ Res1512 d := by
  obtain ⟨h1, h2, h23, h4⟩ := mRank3_cases hd z
  have hlist : RankOneList d ∨ RankTwoList d ∨ RankThreeList d := by
    rcases h4 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · omega
  cases d with
  | A l Q =>
    have hQ : Q.p = 2 := hd.1
    have hcard : ∀ n, Q.exponent = n → Q.card = 2 ^ n := fun n hn => by
      rw [TauCeti.PrimePower.card_def, hQ, hn]
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    · exact absurd hd.2 (by omega)
    · exact absurd hd.2 (by omega)
    · exact Or.inl hQ
    · exact Or.inl hQ
    · have hodd : Odd Q.exponent := by
        rcases hlist with h | h | h <;> first | exact h | exact h.elim
      by_cases hn : Q.exponent = 1
      · exact Or.inl (show Q.card = 2 by rw [hcard 1 hn]; norm_num)
      · right
        refine ⟨by norm_num, by norm_num, hQ, hodd, ?_⟩
        obtain ⟨k, hk⟩ := hodd
        omega
    · have hodd : Odd Q.exponent := by
        rcases hlist with h | h | h <;> first | exact h | exact h.elim
      by_cases hn : Q.exponent = 1
      · exact Or.inl (show Q.card = 2 by rw [hcard 1 hn]; norm_num)
      · right
        refine ⟨by norm_num, by norm_num, hQ, hodd, ?_⟩
        obtain ⟨k, hk⟩ := hodd
        omega
    · have hodd : Odd Q.exponent := by
        rcases hlist with h | h | h <;> first | exact h | exact h.elim
      by_cases hn : Q.exponent = 1
      · exact Or.inl (show Q.card = 2 by rw [hcard 1 hn]; norm_num)
      · right
        refine ⟨by norm_num, by norm_num, hQ, hodd, ?_⟩
        obtain ⟨k, hk⟩ := hodd
        omega
    · exfalso
      rcases hlist with h | h | h <;> exact h.elim
  | twistedA l Q =>
    have hQ : Q.p = 2 := hd.1
    have hexp := Q.exponent_pos
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    · exact absurd hd.2 (by omega)
    · exact absurd hd.2 (by omega)
    · exact absurd hd.2 (by omega)
    · exact Or.inl hQ
    · have hev : Even Q.exponent := by
        rcases hlist with h | h | h <;> first | exact h | exact h.elim
      by_cases hn : Q.exponent = 2
      · exact Or.inl (show Q.card = 4 by rw [TauCeti.PrimePower.card_def, hQ, hn]; norm_num)
      · right
        refine ⟨by norm_num, by norm_num, hQ, hev, ?_⟩
        intro _
        obtain ⟨k, hk⟩ := hev
        omega
    · have hev : Even Q.exponent := by
        rcases hlist with h | h | h <;> first | exact h | exact h.elim
      exact Or.inr ⟨by norm_num, by norm_num, hQ, hev, by omega⟩
    · have hev : Even Q.exponent := by
        rcases hlist with h | h | h <;> first | exact h | exact h.elim
      exact Or.inr ⟨by norm_num, by norm_num, hQ, hev, by omega⟩
    · exfalso
      rcases hlist with h | h | h <;> exact h.elim
  | B l Q =>
    have hQ : Q.p = 2 := hd.1
    rcases l with _ | _ | _ | _ | l
    · exact absurd hd.2 (by omega)
    · exact absurd hd.2 (by omega)
    · exact Or.inl hQ
    · exact Or.inl hQ
    · exfalso
      rcases hlist with h | h | h <;> exact h.elim
  | D l Q =>
    exfalso
    rcases hlist with h | h | h <;> exact h.elim
  | twistedD l Q =>
    have hQ : Q.p = 2 := hd.1
    rcases l with _ | _ | _ | _ | _ | l
    · exact absurd hd.2 (by omega)
    · exact absurd hd.2 (by omega)
    · exact absurd hd.2 (by omega)
    · exact absurd hd.2 (by omega)
    · exact Or.inl hQ
    · exfalso
      rcases hlist with h | h | h <;> exact h.elim
  | G2 Q => exact Or.inl hd
  | C _ _ => exact hd.elim
  | E6 _ => exact hd.elim
  | E7 _ => exact hd.elim
  | E8 _ => exact hd.elim
  | F4 _ => exact hd.elim
  | twistedE6 _ => exact hd.elim
  | trialityD4 _ => exact hd.elim
  | suzuki _ => exact hd.elim
  | reeG2 _ => exact hd.elim
  | reeF4 _ => exact hd.elim
  | tits => exact hd.elim

theorem two_le_mRankChev_three_of_res1512 {d : TauCeti.LieTypeIndex} (hd : Res1512 d) (z : ℕ) :
    2 ≤ mRankChev d 3 z := by
  cases d with
  | A l Q =>
    obtain ⟨h4, h6, hQ, hodd, -⟩ := hd
    have hdr : IsRankTwoPlus (.A l Q) := ⟨hQ, by omega⟩
    interval_cases l
    · have := (mRank3_cases hdr z).2.1.2 hodd
      omega
    · have := (mRank3_cases hdr z).2.2.1.2 hodd
      omega
    · have := (mRank3_cases hdr z).2.2.1.2 hodd
      omega
  | twistedA l Q =>
    obtain ⟨h4, h6, hQ, hev, -⟩ := hd
    have hdr : IsRankTwoPlus (.twistedA l Q) := ⟨hQ, by omega⟩
    interval_cases l
    · have := (mRank3_cases hdr z).2.1.2 hev
      omega
    · have := (mRank3_cases hdr z).2.2.1.2 hev
      omega
    · have := (mRank3_cases hdr z).2.2.1.2 hev
      omega
  | _ => exact hd.elim

theorem exists_prime_four_le_of_res1512_A {l : ℕ} {Q : TauCeti.PrimePower}
    (hd : Res1512 (.A l Q)) (z : ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Q.card - 1 ∧ 4 ≤ mRankChev (.A l Q) q z := by
  obtain ⟨h4, h6, hQ, hodd, h3e⟩ := hd
  have hexp : 2 ≤ Q.exponent := by omega
  rcases exists_prime_rank_ge_four Q.exponent (l + 1) z hexp (by omega) (by omega) with
    ⟨h5, h2, -⟩ | ⟨q, hq, hqd, hqge⟩
  · omega
  · have hdvd : q ∣ 2 ^ Q.exponent - 1 := by
      rw [if_neg (Nat.not_even_iff_odd.2 hodd)] at hqd
      exact hqd
    have hdec : decide (Odd Q.exponent) = true := decide_eq_true hodd
    rw [hdec] at hqge
    refine ⟨q, hq, ?_, ?_, ?_⟩
    · rintro rfl
      obtain ⟨t, ht⟩ := hdvd
      obtain ⟨s, hs⟩ := dvd_pow_self 2 Q.exponent_pos.ne'
      have h1 : 0 < 2 ^ Q.exponent := by positivity
      omega
    · rw [TauCeti.PrimePower.card_def, hQ]
      exact hdvd
    · show 4 ≤ rkLin (l + 1) true Q.card q z
      rw [TauCeti.PrimePower.card_def, hQ]
      exact hqge

theorem exists_prime_four_le_of_res1512_twistedA {l : ℕ} {Q : TauCeti.PrimePower}
    (hd : Res1512 (.twistedA l Q)) (z : ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Q.card + 1 ∧ 4 ≤ mRankChev (.twistedA l Q) q z := by
  obtain ⟨h4, h6, hQ, hev, h4e⟩ := hd
  have hexp : 2 ≤ Q.exponent := by
    obtain ⟨k, hk⟩ := hev
    have hpos := Q.exponent_pos
    omega
  rcases exists_prime_rank_ge_four Q.exponent (l + 1) z hexp (by omega) (by omega) with
    ⟨h5, h2, -⟩ | ⟨q, hq, hqd, hqge⟩
  · have hl : l = 4 := by omega
    have h5e : 4 ≤ Q.exponent := h4e hl
    omega
  · have hdvd : q ∣ 2 ^ Q.exponent + 1 := by
      rw [if_pos hev] at hqd
      exact hqd
    have hdec : decide (Odd Q.exponent) = false :=
      decide_eq_false (Nat.not_odd_iff_even.2 hev)
    rw [hdec] at hqge
    refine ⟨q, hq, ?_, ?_, ?_⟩
    · rintro rfl
      obtain ⟨t, ht⟩ := hdvd
      obtain ⟨s, hs⟩ := dvd_pow_self 2 Q.exponent_pos.ne'
      omega
    · rw [TauCeti.PrimePower.card_def, hQ]
      exact hdvd
    · show 4 ≤ rkLin (l + 1) false Q.card q z
      rw [TauCeti.PrimePower.card_def, hQ]
      exact hqge

theorem in1512_of_ranks_le_three {d : TauCeti.LieTypeIndex} (hd : IsRankTwoPlus d) {z : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → mRankChev d r z ≤ 3) : In1512 d := by
  rcases in1512_or_res1512 hd (h 3 Nat.prime_three (by norm_num)) with hin | hres
  · exact hin
  · cases d with
    | A l Q =>
      obtain ⟨q, hq, hq2, -, hq4⟩ := exists_prime_four_le_of_res1512_A hres z
      have := h q hq hq2
      omega
    | twistedA l Q =>
      obtain ⟨q, hq, hq2, -, hq4⟩ := exists_prime_four_le_of_res1512_twistedA hres z
      have := h q hq hq2
      omega
    | _ => exact hres.elim

theorem not_dvd_of_rank_u5 {Q : TauCeti.PrimePower} (hc : Q.card = 4) {z : ℕ}
    (h : mRankChev (.twistedA 4 Q) 5 z ≤ 3) : ¬ 5 ∣ z := by
  intro h5
  have h1 : mRankChev (.twistedA 4 Q) 5 z = rkLin 5 false Q.card 5 z := rfl
  rw [h1, hc, rank_eq_two_of_in1512_aux_rkLin_false] at h
  have he : eM 4 5 = 1 := by
    have : -((4 : ℕ) : ZMod 5) = 1 := by decide
    unfold eM
    rw [this, orderOf_one]
  rw [if_pos he] at h
  have : ¬ (¬ 5 ∣ z ∧ 5 ∣ 5 ∧ 4 ≤ 5 ∧ padicValNat 5 (4 + 1) ≤ padicValNat 5 5) :=
    fun hc => hc.1 h5
  rw [if_neg this] at h
  omega

theorem dvd_sq_sub_one_of_dvd_add_one_s15 {p Q : ℕ} (h : p ∣ Q + 1) : p ∣ Q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp
  · have h2 : Q ^ 2 - 1 = (Q + 1) * (Q - 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, Q = k + 1 := ⟨Q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [h2]
    exact Dvd.dvd.mul_right h _

theorem dvd_add_one_of_dvd_sq_sub_one {p Q : ℕ} (hp : p.Prime) (hQ : 1 ≤ Q) (h : p ∣ Q ^ 2 - 1)
    (h1 : ¬ p ∣ Q - 1) : p ∣ Q + 1 := by
  have h2 : Q ^ 2 - 1 = (Q + 1) * (Q - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, Q = k + 1 := ⟨Q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [h2] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h3 | h3
  · exact h3
  · exact absurd h3 h1

theorem dvd_of_dvd_card_SL3 {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 0 < m)
    (h : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 m))) :
    p ∣ (2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 m hm.ne'
  rw [Matrix.card_SL_field 3, hq] at h
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ m := ⟨_, rfl⟩
  rw [← hQ] at h
  have hQ2 : 2 ≤ Q := by
    rw [hQ]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hp2' : 2 ^ (2 * m) = Q ^ 2 := by rw [hQ, ← pow_mul, mul_comm]
  have hp3' : 2 ^ (3 * m) = Q ^ 3 := by rw [hQ, ← pow_mul, mul_comm]
  rw [hp2', hp3']
  rw [Fin.prod_univ_three] at h
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h
  have e1 : Q ^ 3 - Q = Q * (Q ^ 2 - 1) := by
    rw [Nat.mul_sub_one]
    congr 1 <;> ring
  have e2 : Q ^ 3 - Q ^ 2 = Q ^ 2 * (Q - 1) := by
    rw [Nat.mul_sub_one]
    congr 1 <;> ring
  have hpos : 0 < Q - 1 := by omega
  rw [e1, e2] at h
  have hdiv : (Q ^ 3 - 1) * (Q * (Q ^ 2 - 1)) * (Q ^ 2 * (Q - 1)) / (Q - 1) =
      (Q ^ 3 - 1) * (Q * (Q ^ 2 - 1)) * Q ^ 2 := by
    have : (Q ^ 3 - 1) * (Q * (Q ^ 2 - 1)) * (Q ^ 2 * (Q - 1)) =
        (Q ^ 3 - 1) * (Q * (Q ^ 2 - 1)) * Q ^ 2 * (Q - 1) := by ring
    rw [this]
    exact Nat.mul_div_cancel _ hpos
  rw [hdiv] at h
  have hnQ : ¬ p ∣ Q := by
    intro hd
    rw [hQ] at hd
    have := (Nat.Prime.dvd_of_dvd_pow hp hd)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact Dvd.dvd.mul_left h2 _
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · exact absurd h3 hnQ
      · exact Dvd.dvd.mul_right h3 _
  · exact absurd (Nat.Prime.dvd_of_dvd_pow hp h1) hnQ

theorem u4_three_rank {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (z : ℕ) :
    2 ≤ mRankChev (.twistedA 3 Q) 3 z ∧ (mRankChev (.twistedA 3 Q) 3 z = 2 → Even Q.exponent) := by
  have hd : IsRankTwoPlus (.twistedA 3 Q) := ⟨hQ, le_refl 3⟩
  obtain ⟨h1, h2, h3, h4⟩ := mRank3_cases hd z
  refine ⟨?_, fun h => h2.1 h⟩
  rcases h4 with h | h | h | h
  · exact absurd h (by simp [RankOneList])
  · have := h2.2 h
    omega
  · have := h3.2 h
    omega
  · omega

end CFSG.LocalAnalysis.RankThreeUC.S15
