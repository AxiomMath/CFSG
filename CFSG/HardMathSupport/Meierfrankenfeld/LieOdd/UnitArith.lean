module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpArith

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem pow_mul_add_le_succ_pow (p k : ℕ) :
    p ^ k * (p + k + 1) ≤ (p + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : p * (p + (k + 1) + 1) ≤ (p + 1) * (p + k + 1) := by nlinarith
    calc p ^ (k + 1) * (p + (k + 1) + 1)
        = p ^ k * (p * (p + (k + 1) + 1)) := by ring
      _ ≤ p ^ k * ((p + 1) * (p + k + 1)) := Nat.mul_le_mul_left _ h1
      _ = (p + 1) * (p ^ k * (p + k + 1)) := by ring
      _ ≤ (p + 1) * (p + 1) ^ (k + 1) := Nat.mul_le_mul_left _ ih
      _ = (p + 1) ^ (k + 1 + 1) := by ring

theorem mul_pow_lt_succ_pow_of_gap {p N E c : ℕ} (hp : 2 ≤ p) (hN : E + 1 ≤ N)
    (hc : c < (N - E) * (p + N)) : c * p ^ E < (p + 1) ^ N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = E + 1 + M := ⟨N - (E + 1), by omega⟩
  rw [show E + 1 + M - E = M + 1 by omega] at hc
  have hM : M < p ^ M := Nat.lt_pow_self (by omega)
  have h := pow_mul_add_le_succ_pow p (E + M)
  have e1 : p + (E + 1 + M) = p + (E + M) + 1 := by ring
  have e2 : E + 1 + M = E + M + 1 := by ring
  calc c * p ^ E < (M + 1) * (p + (E + 1 + M)) * p ^ E :=
        Nat.mul_lt_mul_of_pos_right hc (pow_pos (by omega) _)
    _ ≤ p ^ M * (p + (E + 1 + M)) * p ^ E :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hM)
    _ = p ^ (E + M) * (p + (E + M) + 1) := by rw [pow_add]; rw [e1]; ring
    _ ≤ (p + 1) ^ (E + M + 1) := h
    _ = (p + 1) ^ (E + 1 + M) := by rw [e2]

theorem lt_two_mul_succ_div {p q X : ℕ} (hp : 2 ≤ p) (hd : p - 1 ∣ q - 1) :
    (q - 1) / (p - 1) * X < 2 * ((q - 1) * X / (2 * (p - 1)) + 1) := by
  obtain ⟨A, hA⟩ := hd
  have hA' : (q - 1) / (p - 1) = A := by
    rw [hA, Nat.mul_div_cancel_left _ (by omega : 0 < p - 1)]
  rw [hA', hA]
  have hlt := Nat.lt_mul_div_succ ((p - 1) * A * X) (show 0 < 2 * (p - 1) by omega)
  have key : (p - 1) * (A * X) < (p - 1) * (2 * ((p - 1) * A * X / (2 * (p - 1)) + 1)) := by
    calc (p - 1) * (A * X) = (p - 1) * A * X := by ring
      _ < 2 * (p - 1) * ((p - 1) * A * X / (2 * (p - 1)) + 1) := hlt
      _ = (p - 1) * (2 * ((p - 1) * A * X / (2 * (p - 1)) + 1)) := by ring
  exact Nat.lt_of_mul_lt_mul_left key

theorem two_mul_quad_add_one_le_nine_pow (x : ℕ) (hx : 2 ≤ x) :
    2 * ((x + 1) * (x + 3)) + 1 ≤ 9 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

theorem four_mul_sq_le_three_pow (x : ℕ) (hx : 5 ≤ x) : 4 * (x + 2) ^ 2 ≤ 3 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h3 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
    rw [h3]
    nlinarith [ih, hk]

theorem four_mul_add_one_le_three_pow (e : ℕ) (he : 2 ≤ e) : 4 * e + 1 ≤ 3 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h3 : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
    rw [h3]
    nlinarith [ih, hk]

theorem mul_add_one_le_pow_of_sq (K y e : ℕ) (hy : 9 ≤ y) (hK : 2 * K + 1 ≤ y ^ 2)
    (he : 2 ≤ e) : e * K + 1 ≤ y ^ e := by
  induction e, he using Nat.le_induction with
  | base => simpa using hK
  | succ k hk ih =>
    have h1 : 9 * (k * K + 1) ≤ y ^ k * y := by
      calc 9 * (k * K + 1) = (k * K + 1) * 9 := by ring
        _ ≤ y ^ k * 9 := Nat.mul_le_mul_right 9 ih
        _ ≤ y ^ k * y := Nat.mul_le_mul_left (y ^ k) hy
    rw [pow_succ]
    nlinarith [h1, Nat.mul_le_mul_right K hk]

theorem quad_add_one_le_pow {p e x : ℕ} (hp : 3 ≤ p) (he : 2 ≤ e) (hx : 2 ≤ x) :
    e * ((x + 1) * (x + 3)) + 1 ≤ p ^ (e * x) := by
  have h9 : 9 ≤ 3 ^ x := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ x := Nat.pow_le_pow_right (by norm_num) hx
  have hsq : (3 ^ x) ^ 2 = 9 ^ x := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hpow : 3 ^ (e * x) = (3 ^ x) ^ e := by
    rw [← pow_mul, mul_comm]
  have hK := two_mul_quad_add_one_le_nine_pow x hx
  rw [← hsq] at hK
  calc e * ((x + 1) * (x + 3)) + 1 ≤ (3 ^ x) ^ e :=
        mul_add_one_le_pow_of_sq _ _ e h9 hK he
    _ = 3 ^ (e * x) := hpow.symm
    _ ≤ p ^ (e * x) := Nat.pow_le_pow_left hp _

theorem gap_of_two_mul_add_two {p N E c : ℕ} (hN : 2 * E + 2 ≤ N) (hc : c ≤ 2 * E + 2) :
    E + 1 ≤ N ∧ c < (N - E) * (p + N) := by
  refine ⟨by omega, ?_⟩
  have hA : 2 ≤ N - E := by omega
  calc c ≤ 2 * E + 2 := hc
    _ ≤ N := hN
    _ ≤ p + N := by omega
    _ < 2 * (p + N) := by omega
    _ ≤ (N - E) * (p + N) := Nat.mul_le_mul_right _ hA

theorem gap_n3 {p e N : ℕ} (hp : 3 ≤ p) (he : 2 ≤ e) (hN : 2 * p ^ e ≤ N) :
    8 * e + 1 ≤ N ∧ 12 * e < (N - 8 * e) * (p + N) := by
  have h4 := four_mul_add_one_le_three_pow e he
  have h3p : 3 ^ e ≤ p ^ e := Nat.pow_le_pow_left hp e
  have hA : 8 * e + 1 ≤ N := by omega
  have hB : 2 ≤ N - 8 * e := by omega
  refine ⟨hA, ?_⟩
  calc 12 * e < 2 * N := by omega
    _ ≤ 2 * (p + N) := by omega
    _ ≤ (N - 8 * e) * (p + N) := Nat.mul_le_mul_right _ hB

theorem gap_e_ge_two_n_ge_four {p e n N : ℕ} (hp : 3 ≤ p) (he : 2 ≤ e) (hn : 4 ≤ n)
    (hN : 2 * p ^ (e * (n - 2)) ≤ N) :
    e * (n ^ 2 - 1) + 1 ≤ N ∧ 4 * n * e < (N - e * (n ^ 2 - 1)) * (p + N) := by
  obtain ⟨x, rfl⟩ : ∃ x, n = x + 2 := ⟨n - 2, by omega⟩
  have hx : x + 2 - 2 = x := by omega
  rw [hx] at hN
  have hq := quad_add_one_le_pow hp he (show 2 ≤ x by omega)
  have hsq : (x + 2) ^ 2 - 1 = (x + 1) * (x + 3) := by
    have : (x + 2) ^ 2 = (x + 1) * (x + 3) + 1 := by ring
    omega
  rw [hsq]
  have hE : 2 * (e * ((x + 1) * (x + 3))) + 2 ≤ N := by
    generalize e * ((x + 1) * (x + 3)) = E at hq ⊢
    omega
  have hK : 2 * (x + 2) ≤ (x + 1) * (x + 3) := by nlinarith
  have hK2 := Nat.mul_le_mul_left e hK
  have hc : 4 * (x + 2) * e ≤ 2 * (e * ((x + 1) * (x + 3))) + 2 := by nlinarith [hK2]
  exact gap_of_two_mul_add_two (p := p) hE hc

theorem gap_e_one {p n N : ℕ} (hn : 2 ≤ n) (hN : 2 * n ^ 2 ≤ N) :
    n ^ 2 - 1 + 1 ≤ N ∧ 4 * n < (N - (n ^ 2 - 1)) * (p + N) := by
  have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hE : 2 * (n ^ 2 - 1) + 2 = 2 * n ^ 2 := by omega
  have hc : 4 * n ≤ 2 * (n ^ 2 - 1) + 2 := by
    rw [hE]; nlinarith
  exact gap_of_two_mul_add_two (p := p) (by omega) hc

theorem four_le_quot {p e : ℕ} (hp : 3 ≤ p) (he : 2 ≤ e) : 4 ≤ (p ^ e - 1) / (p - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 1 := ⟨p - 1, by omega⟩
  have hd : d + 1 - 1 = d := by omega
  rw [hd, Nat.le_div_iff_mul_le (by omega)]
  have h2 : (d + 1) ^ 2 ≤ (d + 1) ^ e := Nat.pow_le_pow_right (by omega) he
  have h3 : 4 * d + 1 ≤ (d + 1) ^ e := by nlinarith
  omega

theorem two_mul_le_of_four_le_mul {A X N : ℕ} (hA : 4 ≤ A) (h : A * X < 2 * (N + 1)) :
    2 * X ≤ N := by
  have h4 := Nat.mul_le_mul_right X hA
  generalize A * X = T at h4 h
  omega

theorem four_mul_sq_le_pow_of_odd {p n : ℕ} (hodd : p % 2 = 1) (hp : 3 ≤ p) (hn : 4 ≤ n)
    (h4 : ¬(n = 4 ∧ p = 3)) (h5 : ¬(n = 5 ∧ p = 3)) (hspec : ¬(n = 4 ∧ p = 5)) :
    4 * n ^ 2 ≤ p ^ (n - 2) ∨ (n = 4 ∧ p = 7) ∨ (n = 6 ∧ p = 3) := by
  obtain ⟨x, rfl⟩ : ∃ x, n = x + 2 := ⟨n - 2, by omega⟩
  have hx2 : x + 2 - 2 = x := by omega
  rw [hx2]
  rcases (show x = 2 ∨ x = 3 ∨ x = 4 ∨ 5 ≤ x by omega) with rfl | rfl | rfl | hx
  · rcases (show p = 3 ∨ p = 5 ∨ p = 7 ∨ 9 ≤ p by omega) with rfl | rfl | rfl | hp9
    · exact absurd ⟨rfl, rfl⟩ h4
    · exact absurd ⟨rfl, rfl⟩ hspec
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · left
      nlinarith
  · rcases (show p = 3 ∨ 5 ≤ p by omega) with rfl | hp5
    · exact absurd ⟨rfl, rfl⟩ h5
    · left
      calc 4 * (3 + 2) ^ 2 = 100 := by norm_num
        _ ≤ 5 ^ 3 := by norm_num
        _ ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
  · rcases (show p = 3 ∨ 5 ≤ p by omega) with rfl | hp5
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · left
      calc 4 * (4 + 2) ^ 2 = 144 := by norm_num
        _ ≤ 5 ^ 4 := by norm_num
        _ ≤ p ^ 4 := Nat.pow_le_pow_left hp5 4
  · left
    exact (four_mul_sq_le_three_pow x hx).trans (Nat.pow_le_pow_left hp x)

theorem card_aut_psun_lt {p e n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (hn : 3 ≤ n)
    (h3 : ¬ (n = 3 ∧ e = 1)) (h4 : ¬ (n = 4 ∧ p ^ e = 3)) (h5 : ¬ (n = 5 ∧ p ^ e = 3)) :
    4 * n * e * (p ^ e) ^ (n ^ 2 - 1) <
      2 ^ (orderOf (2 : ZMod p) * ((p ^ e - 1) * (p ^ e) ^ (n - 2) / (2 * (p - 1)))) := by
  have hpp : p.Prime := Fact.out
  have hp2' : 2 ≤ p := hpp.two_le
  have hp3 : 3 ≤ p := by omega
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two hp2)
  by_cases hexc : e = 1 ∧ n = 4 ∧ p = 5
  · obtain ⟨rfl, rfl, rfl⟩ := hexc
    rw [orderOf_two_zmod_five]
    norm_num
  · have hd : p - 1 ∣ p ^ e - 1 := by
      have := Nat.sub_dvd_pow_sub_pow p 1 e
      rwa [one_pow] at this
    obtain ⟨N, hN⟩ : ∃ N, N = (p ^ e - 1) * (p ^ e) ^ (n - 2) / (2 * (p - 1)) := ⟨_, rfl⟩
    rw [← hN]
    have hord : p + 1 ≤ 2 ^ orderOf (2 : ZMod p) := succ_le_two_pow_orderOf hp2
    have hlt := lt_two_mul_succ_div (X := (p ^ e) ^ (n - 2)) hp2' hd
    rw [← hN] at hlt
    have hX : (p ^ e) ^ (n - 2) = p ^ (e * (n - 2)) := (pow_mul p e (n - 2)).symm
    have hgap : 4 * n * e * p ^ (e * (n ^ 2 - 1)) < (p + 1) ^ N := by
      rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | he2
      · have hn4 : 4 ≤ n := by
          by_contra hc
          exact h3 ⟨by omega, rfl⟩
        simp only [pow_one] at hN
        rw [mul_comm 2 (p - 1), Nat.mul_div_mul_left _ _ (by omega : 0 < p - 1)] at hN
        have hsq := four_mul_sq_le_pow_of_odd hodd hp3 hn4
          (fun h => h4 ⟨h.1, by rw [pow_one]; exact h.2⟩)
          (fun h => h5 ⟨h.1, by rw [pow_one]; exact h.2⟩)
          (fun h => hexc ⟨rfl, h⟩)
        rcases hsq with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hN2 : 2 * n ^ 2 ≤ N := by
            rw [hN]
            omega
          obtain ⟨hE, hc⟩ := gap_e_one (p := p) (by omega : 2 ≤ n) hN2
          have key := mul_pow_lt_succ_pow_of_gap (E := n ^ 2 - 1) (c := 4 * n) hp2' hE hc
          rw [mul_one, one_mul]
          exact key
        · rw [hN]
          norm_num
        · rw [hN]
          norm_num
      · have hA := four_le_quot hp3 he2
        have h2X := two_mul_le_of_four_le_mul hA hlt
        rw [hX] at h2X
        rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
        · have hN2 : 2 * p ^ e ≤ N := by
            have h1 : e * (3 - 2) = e := by norm_num
            rw [h1] at h2X
            exact h2X
          obtain ⟨hE, hc⟩ := gap_n3 hp3 he2 hN2
          have key := mul_pow_lt_succ_pow_of_gap (E := 8 * e) (c := 4 * 3 * e) hp2' hE
            (lt_of_eq_of_lt (by ring) hc)
          have hE8 : e * (3 ^ 2 - 1) = 8 * e := by
            norm_num
            ring
          rw [hE8]
          exact key
        · have hN2 : 2 * p ^ (e * (n - 2)) ≤ N := h2X
          obtain ⟨hE, hc⟩ := gap_e_ge_two_n_ge_four hp3 he2 hn4 hN2
          exact mul_pow_lt_succ_pow_of_gap hp2' hE hc
    calc 4 * n * e * (p ^ e) ^ (n ^ 2 - 1) = 4 * n * e * p ^ (e * (n ^ 2 - 1)) := by
          rw [← pow_mul]
      _ < (p + 1) ^ N := hgap
      _ ≤ (2 ^ orderOf (2 : ZMod p)) ^ N := Nat.pow_le_pow_left hord N
      _ = 2 ^ (orderOf (2 : ZMod p) * N) := by rw [pow_mul]

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
