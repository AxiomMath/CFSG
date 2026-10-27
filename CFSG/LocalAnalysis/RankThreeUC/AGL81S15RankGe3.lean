module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem rank_ge_three_of_in1512_auxLin {m : ℕ} (hm : m ≤ 7) {eps : Bool} {Q p z : ℕ}
    (h : 3 ≤ rkLin m eps Q p z) :
    ((if eps then eP Q p else eM Q p) = 1 ∧ 4 ≤ m) ∨
      ((if eps then eP Q p else eM Q p) = 2 ∧ 6 ≤ m) := by
  unfold rkLin at h
  generalize (if eps then eP Q p else eM Q p) = e at h ⊢
  by_cases he : e = 1
  · subst he
    left
    refine ⟨rfl, ?_⟩
    rw [if_pos rfl] at h
    split_ifs at h <;> omega
  · rw [if_neg he] at h
    right
    rcases Nat.lt_or_ge e 2 with he2 | he2
    · have he0 : e = 0 := by omega
      subst he0
      simp at h
    · have h3 : 3 * e ≤ m := (Nat.le_div_iff_mul_le (by omega)).mp h
      exact ⟨by omega, by omega⟩

theorem rank_ge_three_of_in1512_auxP2 {Q p : ℕ} (hQ : 1 ≤ Q) (h : eP Q p = 2) :
    p ∣ Q ^ 2 - 1 := by
  have h1 : eS Q p = 1 := by
    rw [eS_eq_eP_div_gcd, h]
    norm_num
  exact (eS_eq_one_iff hQ).mp h1

theorem rank_ge_three_of_in1512_auxDiv {m e : ℕ} (hm : m ≤ 5) (h : 3 ≤ m / e) : e = 1 := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    simp at h
  · have h3 : 3 * e ≤ m := (Nat.le_div_iff_mul_le he).mp h
    omega

theorem rank_ge_three_of_in1512_auxNotDvdOne {p : ℕ} (hp5 : 5 ≤ p) : ¬ p ∣ 1 := fun hd =>
  absurd (Nat.le_of_dvd one_pos hd) (by omega)

theorem rank_ge_three_of_in1512_auxNotDvdThree {p : ℕ} (hp5 : 5 ≤ p) : ¬ p ∣ 3 := fun hd =>
  absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)

theorem rank_ge_three_of_in1512_auxCard (Q : TauCeti.PrimePower) : 1 ≤ Q.card := by
  have := Q.isPrimePow_card.two_le
  omega

theorem rank_ge_three_of_in1512 {d : TauCeti.LieTypeIndex} (hd : In1512 d) {p z : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (h : 3 ≤ mRankChev d p z) :
    (∃ Q, d = .A 3 Q ∧ p ∣ Q.card - 1) ∨ (∃ Q, d = .twistedA 3 Q ∧ p ∣ Q.card + 1) ∨
    (∃ Q, (d = .B 3 Q ∨ d = .twistedD 4 Q) ∧ p ∣ Q.card ^ 2 - 1) ∨
    (∃ Q, d = .twistedA 4 Q ∧ Q.card = 4 ∧ p = 5) := by
  cases d with
  | A rank Q =>
    have hr : rank = 2 ∨ rank = 3 ∨ rank = 4 ∨ rank = 5 ∨ rank = 6 := by
      rcases rank with _ | _ | _ | _ | _ | _ | _ | n <;> simp only [In1512] at hd <;> omega
    have hQ := rank_ge_three_of_in1512_auxCard Q
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · change 3 ≤ rkLin 3 true Q.card p z at h
      rcases rank_ge_three_of_in1512_auxLin (by norm_num) h with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    · change 3 ≤ rkLin 4 true Q.card p z at h
      rcases rank_ge_three_of_in1512_auxLin (by norm_num) h with ⟨he, _⟩ | ⟨_, _⟩
      · exact Or.inl ⟨Q, rfl, (eP_eq_one_iff hQ).mp he⟩
      · omega
    · simp only [In1512] at hd
      change 3 ≤ rkLin 5 true Q.card p z at h
      rcases rank_ge_three_of_in1512_auxLin (by norm_num) h with ⟨he, _⟩ | ⟨_, _⟩
      · have h1 := (eP_eq_one_iff hQ).mp he
        rw [hd] at h1
        exact absurd h1 (rank_ge_three_of_in1512_auxNotDvdOne hp5)
      · omega
    · simp only [In1512] at hd
      change 3 ≤ rkLin 6 true Q.card p z at h
      rcases rank_ge_three_of_in1512_auxLin (by norm_num) h with ⟨he, _⟩ | ⟨he, _⟩
      · have h1 := (eP_eq_one_iff hQ).mp he
        rw [hd] at h1
        exact absurd h1 (rank_ge_three_of_in1512_auxNotDvdOne hp5)
      · have h1 := rank_ge_three_of_in1512_auxP2 hQ he
        rw [hd] at h1
        exact absurd h1 (rank_ge_three_of_in1512_auxNotDvdThree hp5)
    · simp only [In1512] at hd
      change 3 ≤ rkLin 7 true Q.card p z at h
      rcases rank_ge_three_of_in1512_auxLin (by norm_num) h with ⟨he, _⟩ | ⟨he, _⟩
      · have h1 := (eP_eq_one_iff hQ).mp he
        rw [hd] at h1
        exact absurd h1 (rank_ge_three_of_in1512_auxNotDvdOne hp5)
      · have h1 := rank_ge_three_of_in1512_auxP2 hQ he
        rw [hd] at h1
        exact absurd h1 (rank_ge_three_of_in1512_auxNotDvdThree hp5)
  | twistedA rank Q =>
    have hr : rank = 3 ∨ rank = 4 := by
      rcases rank with _ | _ | _ | _ | _ | n <;> simp only [In1512] at hd <;> omega
    rcases hr with rfl | rfl
    · change 3 ≤ rkLin 4 false Q.card p z at h
      rcases rank_ge_three_of_in1512_auxLin (by norm_num) h with ⟨he, _⟩ | ⟨_, _⟩
      · exact Or.inr (Or.inl ⟨Q, rfl, eM_eq_one_iff.mp he⟩)
      · omega
    · simp only [In1512] at hd
      change 3 ≤ rkLin 5 false Q.card p z at h
      rcases rank_ge_three_of_in1512_auxLin (by norm_num) h with ⟨he, _⟩ | ⟨_, _⟩
      · have h1 := eM_eq_one_iff.mp he
        rw [hd] at h1
        exact Or.inr (Or.inr (Or.inr ⟨Q, rfl, hd,
          (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h1⟩))
      · omega
  | B rank Q =>
    have hr : rank = 2 ∨ rank = 3 := by
      rcases rank with _ | _ | _ | _ | n <;> simp only [In1512] at hd <;> omega
    have hQ := rank_ge_three_of_in1512_auxCard Q
    rcases hr with rfl | rfl
    · change 3 ≤ 2 / eS Q.card p at h
      have := Nat.div_le_self 2 (eS Q.card p)
      omega
    · change 3 ≤ 3 / eS Q.card p at h
      have h1 := rank_ge_three_of_in1512_auxDiv (by norm_num) h
      exact Or.inr (Or.inr (Or.inl ⟨Q, Or.inl rfl, (eS_eq_one_iff hQ).mp h1⟩))
  | twistedD rank Q =>
    have hr : rank = 4 := by
      rcases rank with _ | _ | _ | _ | _ | n <;> simp only [In1512] at hd <;> omega
    have hQ := rank_ge_three_of_in1512_auxCard Q
    subst hr
    change 3 ≤ 4 / eS Q.card p - (if eP Q.card p ∣ 4 then 1 else 0) at h
    have h1 := rank_ge_three_of_in1512_auxDiv (m := 4) (e := eS Q.card p) (by norm_num) (by omega)
    exact Or.inr (Or.inr (Or.inl ⟨Q, Or.inr rfl, (eS_eq_one_iff hQ).mp h1⟩))
  | G2 Q =>
    change 3 ≤ rkG2 Q.card p at h
    unfold rkG2 at h
    split_ifs at h <;> omega
  | C _ _ => simp only [In1512] at hd
  | D _ _ => simp only [In1512] at hd
  | E6 _ => simp only [In1512] at hd
  | E7 _ => simp only [In1512] at hd
  | E8 _ => simp only [In1512] at hd
  | F4 _ => simp only [In1512] at hd
  | twistedE6 _ => simp only [In1512] at hd
  | trialityD4 _ => simp only [In1512] at hd
  | suzuki _ => simp only [In1512] at hd
  | reeG2 _ => simp only [In1512] at hd
  | reeF4 _ => simp only [In1512] at hd
  | tits => simp only [In1512] at hd

end CFSG.LocalAnalysis.RankThreeUC.S15
