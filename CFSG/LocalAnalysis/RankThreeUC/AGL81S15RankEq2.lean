module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem rank_eq_two_of_in1512_aux_div {n e k : ℕ} (hk : 0 < k) (h : n / e = k) :
    k * e ≤ n ∧ n < (k + 1) * e := by
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · rw [Nat.div_zero] at h; omega
    · exact he
  have h1 := Nat.div_add_mod n e
  have h2 := Nat.mod_lt n he
  rw [h] at h1
  have h3 : k * e = e * k := Nat.mul_comm k e
  have h4 : (k + 1) * e = e * k + e := by ring
  constructor <;> omega

theorem rank_eq_two_of_in1512_aux_rkLin_true (m Q r z : ℕ) : rkLin m true Q r z =
    if eP Q r = 1 then
      m - 1 - (if ¬ r ∣ z ∧ r ∣ m ∧ 4 ≤ m ∧ padicValNat r (Q - 1) ≤ padicValNat r m then 1 else 0)
    else m / eP Q r := rfl

theorem rank_eq_two_of_in1512_aux_rkLin_false (m Q r z : ℕ) : rkLin m false Q r z =
    if eM Q r = 1 then
      m - 1 - (if ¬ r ∣ z ∧ r ∣ m ∧ 4 ≤ m ∧ padicValNat r (Q + 1) ≤ padicValNat r m then 1 else 0)
    else m / eM Q r := rfl

theorem rank_eq_two_of_in1512_aux_eP {Q p : ℕ} (hp : p.Prime) (h : eP Q p = 2) : p ∣ Q + 1 := by
  have h2 : (Q : ZMod p) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (Q : ZMod p)
    unfold eP at h
    rwa [h] at this
  have h1 : (Q : ZMod p) ≠ 1 := by
    intro h1
    unfold eP at h
    rw [h1, orderOf_one] at h
    omega
  haveI := Fact.mk hp
  rcases sq_eq_one_iff.mp h2 with h3 | h3
  · exact absurd h3 h1
  · rw [← CharP.cast_eq_zero_iff (ZMod p) p (Q + 1), Nat.cast_add, Nat.cast_one, h3]
    simp

theorem rank_eq_two_of_in1512_aux_eM {Q p : ℕ} (hp : p.Prime) (hQ : 1 ≤ Q) (h : eM Q p = 2) :
    p ∣ Q - 1 := by
  have h2 : (-(Q : ZMod p)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (-(Q : ZMod p))
    unfold eM at h
    rwa [h] at this
  have h1 : -(Q : ZMod p) ≠ 1 := by
    intro h1
    unfold eM at h
    rw [h1, orderOf_one] at h
    omega
  haveI := Fact.mk hp
  rcases sq_eq_one_iff.mp h2 with h3 | h3
  · exact absurd h3 h1
  · exact (eP_eq_one_iff hQ).mp (orderOf_eq_one_iff.mpr (neg_inj.mp h3))

theorem rank_eq_two_of_in1512_aux_eS {Q p : ℕ} (h : eS Q p = 2) : eP Q p ∣ 4 := by
  apply orderOf_dvd_of_pow_eq_one
  have := pow_orderOf_eq_one ((Q : ZMod p) ^ 2)
  unfold eS at h
  rw [h, ← pow_mul] at this
  exact this

theorem rank_eq_two_of_in1512_aux_dvd_pow {Q p : ℕ} (hQ : 1 ≤ Q) : p ∣ Q ^ eP Q p - 1 := by
  have h1 : (Q : ZMod p) ^ eP Q p = 1 := pow_orderOf_eq_one _
  rw [← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_sub (Nat.one_le_pow _ _ hQ), Nat.cast_pow, h1,
    Nat.cast_one, sub_self]

theorem rank_eq_two_of_in1512_aux_eM_sq {Q p : ℕ} (hQ : 1 ≤ Q) (h : eM Q p = 2) :
    p ∣ Q ^ 2 - 1 := by
  have h1 : (-(Q : ZMod p)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (-(Q : ZMod p))
    unfold eM at h
    rwa [h] at this
  have h2 : (Q : ZMod p) ^ 2 = 1 := by rw [← neg_sq]; exact h1
  rw [← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_sub (Nat.one_le_pow _ _ hQ), Nat.cast_pow, h2,
    Nat.cast_one, sub_self]

theorem rank_eq_two_of_in1512_aux_G2 {Q p : ℕ} (hQ : 1 ≤ Q) (h : rkG2 Q p = 2) :
    p ∣ Q ^ 2 - 1 := by
  unfold rkG2 at h
  by_cases h1 : eS Q p = 1
  · exact (eS_eq_one_iff hQ).mp h1
  · rw [if_neg h1] at h
    split_ifs at h <;> omega

theorem rank_eq_two_of_in1512_aux_B2 {Q p : ℕ} (hQ : 1 ≤ Q) (h : rkSp 2 Q p = 2) :
    p ∣ Q ^ 2 - 1 := by
  unfold rkSp at h
  have := rank_eq_two_of_in1512_aux_div (by norm_num) h
  apply (eS_eq_one_iff hQ).mp
  omega

theorem rank_eq_two_of_in1512_aux_B3 {Q p : ℕ} (h : rkSp 3 Q p = 2) : False := by
  unfold rkSp at h
  have := rank_eq_two_of_in1512_aux_div (by norm_num) h
  omega

theorem rank_eq_two_of_in1512_aux_D4 {Q p : ℕ} (h : rkOmMinus 4 Q p = 2) : False := by
  unfold rkOmMinus at h
  split_ifs at h with hdvd
  · have := rank_eq_two_of_in1512_aux_div (n := 4) (e := eS Q p) (k := 3) (by norm_num)
      (by omega)
    omega
  · have h2 := rank_eq_two_of_in1512_aux_div (by norm_num) (show 4 / eS Q p = 2 by omega)
    have : eS Q p = 2 := by omega
    exact hdvd (rank_eq_two_of_in1512_aux_eS this)

theorem rank_eq_two_of_in1512_aux_A3 {Q p z : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : rkLin 4 true Q p z = 2) : p ∣ Q + 1 := by
  have h4 : ¬ p ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  rw [rank_eq_two_of_in1512_aux_rkLin_true] at h
  by_cases h1 : eP Q p = 1
  · rw [if_pos h1] at h
    have hδ : ¬ (¬ p ∣ z ∧ p ∣ 4 ∧ 4 ≤ 4 ∧ padicValNat p (Q - 1) ≤ padicValNat p 4) :=
      fun hc => h4 hc.2.1
    rw [if_neg hδ] at h
    omega
  · rw [if_neg h1] at h
    have h2 := rank_eq_two_of_in1512_aux_div (by norm_num) h
    have : eP Q p = 2 := by omega
    exact rank_eq_two_of_in1512_aux_eP hp this

theorem rank_eq_two_of_in1512_aux_U4 {Q p z : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : 1 ≤ Q)
    (h : rkLin 4 false Q p z = 2) : p ∣ Q - 1 := by
  have h4 : ¬ p ∣ 4 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  rw [rank_eq_two_of_in1512_aux_rkLin_false] at h
  by_cases h1 : eM Q p = 1
  · rw [if_pos h1] at h
    have hδ : ¬ (¬ p ∣ z ∧ p ∣ 4 ∧ 4 ≤ 4 ∧ padicValNat p (Q + 1) ≤ padicValNat p 4) :=
      fun hc => h4 hc.2.1
    rw [if_neg hδ] at h
    omega
  · rw [if_neg h1] at h
    have h2 := rank_eq_two_of_in1512_aux_div (by norm_num) h
    have : eM Q p = 2 := by omega
    exact rank_eq_two_of_in1512_aux_eM hp hQ this

theorem rank_eq_two_of_in1512_aux_A2 {Q p z : ℕ} (hQ : 1 ≤ Q) (h : rkLin 3 true Q p z = 2) :
    p ∣ Q - 1 := by
  rw [rank_eq_two_of_in1512_aux_rkLin_true] at h
  by_cases h1 : eP Q p = 1
  · exact (eP_eq_one_iff hQ).mp h1
  · rw [if_neg h1] at h
    have h2 := rank_eq_two_of_in1512_aux_div (by norm_num) h
    exfalso
    omega

theorem rank_eq_two_of_in1512_aux_eP_two_ne_one {p : ℕ} (hp5 : 5 ≤ p) : eP 2 p ≠ 1 := by
  intro h
  have h1 := (eP_eq_one_iff (by norm_num : 1 ≤ 2)).mp h
  have := Nat.le_of_dvd (by norm_num) h1
  omega

theorem rank_eq_two_of_in1512_aux_L5 {p z : ℕ} (hp5 : 5 ≤ p) (h : rkLin 5 true 2 p z = 2) :
    False := by
  rw [rank_eq_two_of_in1512_aux_rkLin_true,
    if_neg (rank_eq_two_of_in1512_aux_eP_two_ne_one hp5)] at h
  have h2 := rank_eq_two_of_in1512_aux_div (by norm_num) h
  have he : eP 2 p = 2 := by omega
  have h3 := rank_eq_two_of_in1512_aux_dvd_pow (Q := 2) (p := p) (by norm_num)
  rw [he] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem rank_eq_two_of_in1512_aux_L6 {p z : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : rkLin 6 true 2 p z = 2) : p = 7 := by
  rw [rank_eq_two_of_in1512_aux_rkLin_true,
    if_neg (rank_eq_two_of_in1512_aux_eP_two_ne_one hp5)] at h
  have h2 := rank_eq_two_of_in1512_aux_div (by norm_num) h
  have he : eP 2 p = 3 := by omega
  have h3 := rank_eq_two_of_in1512_aux_dvd_pow (Q := 2) (p := p) (by norm_num)
  rw [he] at h3
  exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (by simpa using h3)

theorem rank_eq_two_of_in1512_aux_L7 {p z : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : rkLin 7 true 2 p z = 2) : p = 7 := by
  rw [rank_eq_two_of_in1512_aux_rkLin_true,
    if_neg (rank_eq_two_of_in1512_aux_eP_two_ne_one hp5)] at h
  have h2 := rank_eq_two_of_in1512_aux_div (by norm_num) h
  have he : eP 2 p = 3 := by omega
  have h3 := rank_eq_two_of_in1512_aux_dvd_pow (Q := 2) (p := p) (by norm_num)
  rw [he] at h3
  exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (by simpa using h3)

theorem rank_eq_two_of_in1512_aux_U5 {p z : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : rkLin 5 false 4 p z = 2) : False := by
  rw [rank_eq_two_of_in1512_aux_rkLin_false] at h
  by_cases h1 : eM 4 p = 1
  · rw [if_pos h1] at h
    split_ifs at h <;> omega
  · rw [if_neg h1] at h
    have h2 := rank_eq_two_of_in1512_aux_div (by norm_num) h
    have he : eM 4 p = 2 := by omega
    have h3 := rank_eq_two_of_in1512_aux_eM_sq (by norm_num) he
    have h15 : p ∣ 3 * 5 := by simpa using h3
    have h5 : p = 5 := by
      rcases (Nat.Prime.dvd_mul hp).mp h15 with h3' | h5'
      · have := Nat.le_of_dvd (by norm_num) h3'
        omega
      · have := Nat.le_of_dvd (by norm_num) h5'
        omega
    subst h5
    rw [eM_4_5] at he
    omega

theorem rank_eq_two_of_in1512 {d : TauCeti.LieTypeIndex} (hd : In1512 d) {p z : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (h : mRankChev d p z = 2) :
    (∃ Q, (d = .G2 Q ∨ d = .B 2 Q) ∧ p ∣ Q.card ^ 2 - 1) ∨
    (∃ Q, d = .A 3 Q ∧ p ∣ Q.card + 1) ∨ (∃ Q, d = .twistedA 3 Q ∧ p ∣ Q.card - 1) ∨
    (∃ Q, d = .A 2 Q ∧ p ∣ Q.card - 1) ∨
    (∃ Q, (d = .A 5 Q ∨ d = .A 6 Q) ∧ Q.card = 2 ∧ p = 7) := by
  cases d with
  | A l Q =>
    have hQ : 1 ≤ Q.card := Q.isPrimePow_card.pos
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    · simp [In1512] at hd
    · simp [In1512] at hd
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨Q, rfl, rank_eq_two_of_in1512_aux_A2 hQ h⟩)))
    · exact Or.inr (Or.inl ⟨Q, rfl, rank_eq_two_of_in1512_aux_A3 hp hp5 h⟩)
    · have hc : Q.card = 2 := by simpa [In1512] using hd
      have h' : rkLin 5 true Q.card p z = 2 := h
      rw [hc] at h'
      exact (rank_eq_two_of_in1512_aux_L5 hp5 h').elim
    · have hc : Q.card = 2 := by simpa [In1512] using hd
      have h' : rkLin 6 true Q.card p z = 2 := h
      rw [hc] at h'
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨Q, Or.inl rfl, hc, rank_eq_two_of_in1512_aux_L6 hp hp5 h'⟩)))
    · have hc : Q.card = 2 := by simpa [In1512] using hd
      have h' : rkLin 7 true Q.card p z = 2 := h
      rw [hc] at h'
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨Q, Or.inr rfl, hc, rank_eq_two_of_in1512_aux_L7 hp hp5 h'⟩)))
    · simp [In1512] at hd
  | twistedA l Q =>
    have hQ : 1 ≤ Q.card := Q.isPrimePow_card.pos
    rcases l with _ | _ | _ | _ | _ | l
    · simp [In1512] at hd
    · simp [In1512] at hd
    · simp [In1512] at hd
    · exact Or.inr (Or.inr (Or.inl ⟨Q, rfl, rank_eq_two_of_in1512_aux_U4 hp hp5 hQ h⟩))
    · have hc : Q.card = 4 := by simpa [In1512] using hd
      have h' : rkLin 5 false Q.card p z = 2 := h
      rw [hc] at h'
      exact (rank_eq_two_of_in1512_aux_U5 hp hp5 h').elim
    · simp [In1512] at hd
  | B l Q =>
    have hQ : 1 ≤ Q.card := Q.isPrimePow_card.pos
    rcases l with _ | _ | _ | _ | l
    · simp [In1512] at hd
    · simp [In1512] at hd
    · exact Or.inl ⟨Q, Or.inr rfl, rank_eq_two_of_in1512_aux_B2 hQ h⟩
    · exact (rank_eq_two_of_in1512_aux_B3 h).elim
    · simp [In1512] at hd
  | C _ _ => simp [In1512] at hd
  | D _ _ => simp [In1512] at hd
  | twistedD l Q =>
    rcases l with _ | _ | _ | _ | _ | l
    · simp [In1512] at hd
    · simp [In1512] at hd
    · simp [In1512] at hd
    · simp [In1512] at hd
    · exact (rank_eq_two_of_in1512_aux_D4 h).elim
    · simp [In1512] at hd
  | E6 _ => simp [In1512] at hd
  | E7 _ => simp [In1512] at hd
  | E8 _ => simp [In1512] at hd
  | F4 _ => simp [In1512] at hd
  | G2 Q =>
    have hQ : 1 ≤ Q.card := Q.isPrimePow_card.pos
    exact Or.inl ⟨Q, Or.inl rfl, rank_eq_two_of_in1512_aux_G2 hQ h⟩
  | twistedE6 _ => simp [In1512] at hd
  | trialityD4 _ => simp [In1512] at hd
  | suzuki _ => simp [In1512] at hd
  | reeG2 _ => simp [In1512] at hd
  | reeF4 _ => simp [In1512] at hd
  | tits => simp [In1512] at hd

end CFSG.LocalAnalysis.RankThreeUC.S15
