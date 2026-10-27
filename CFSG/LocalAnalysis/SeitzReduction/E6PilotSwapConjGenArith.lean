module

public import CFSG.Open.Defs

public section

namespace CFSG.SeitzReduction.E6Pilot

open CFSG.Open

@[expose] def numE6 (x : ℕ) : ℕ :=
  x ^ 36 * (x ^ 12 - 1) * (x ^ 9 - 1) * (x ^ 8 - 1) * (x ^ 6 - 1) * (x ^ 5 - 1) * (x ^ 2 - 1)

@[expose] def numTwistedE6 (x : ℕ) : ℕ :=
  x ^ 36 * (x ^ 12 - 1) * (x ^ 9 + 1) * (x ^ 8 - 1) * (x ^ 6 - 1) * (x ^ 5 + 1) * (x ^ 2 - 1)

@[expose] def ratE6 (x : ℕ) : ℕ :=
  x ^ 36 * (x ^ 12 + 1) * (x ^ 9 + 1) * (x ^ 8 + 1) * (x ^ 6 + 1) * (x ^ 5 + 1) * (x ^ 2 + 1)

@[expose] def ratTwistedE6 (x : ℕ) : ℕ :=
  x ^ 36 * (x ^ 12 + 1) * (x ^ 9 - 1) * (x ^ 8 + 1) * (x ^ 6 + 1) * (x ^ 5 - 1) * (x ^ 2 + 1)

theorem numE6_sq {x : ℕ} (hx : 1 ≤ x) : numE6 (x ^ 2) = numE6 x * ratE6 x := by
  have h : ∀ k, 1 ≤ x ^ k := fun k => Nat.one_le_pow _ _ hx
  have h' : ∀ k, 1 ≤ (x ^ 2) ^ k := fun k => Nat.one_le_pow _ _ (h 2)
  unfold numE6 ratE6
  zify [h 12, h 9, h 8, h 6, h 5, h 2, h' 12, h' 9, h' 8, h' 6, h' 5, h' 2]
  ring

theorem numE6_sq' {x : ℕ} (hx : 1 ≤ x) : numE6 (x ^ 2) = numTwistedE6 x * ratTwistedE6 x := by
  have h : ∀ k, 1 ≤ x ^ k := fun k => Nat.one_le_pow _ _ hx
  have h' : ∀ k, 1 ≤ (x ^ 2) ^ k := fun k => Nat.one_le_pow _ _ (h 2)
  unfold numE6 numTwistedE6 ratTwistedE6
  zify [h 12, h 9, h 8, h 6, h 5, h 2, h' 12, h' 9, h' 8, h' 6, h' 5, h' 2]
  ring

theorem coprime_of_dvd_of_add_two {a b c : ℕ} (ha : Odd a) (h : b + 2 = c ∨ c + 2 = b)
    (hb : a ∣ b) : Nat.Coprime a c := by
  have h1 : Nat.gcd a c ∣ b := (Nat.gcd_dvd_left a c).trans hb
  have h2 : Nat.gcd a c ∣ c := Nat.gcd_dvd_right a c
  have h3 : Nat.gcd a c ∣ 2 := by
    rcases h with rfl | rfl
    · exact (Nat.dvd_add_right h1).1 h2
    · exact (Nat.dvd_add_right h2).1 h1
  have h4 : Odd (Nat.gcd a c) := ha.of_dvd_nat (Nat.gcd_dvd_left _ _)
  rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h | h
  · exact h
  · rw [h] at h4
    exact absurd h4 (by decide)

theorem coprime_sub_one_pow_add_one {x : ℕ} (hx : Even x) (hx1 : 1 ≤ x) (d : ℕ) :
    Nat.Coprime (x - 1) (x ^ d + 1) := by
  have hodd : Odd (x - 1) := by
    obtain ⟨r, rfl⟩ := hx
    exact ⟨r - 1, by omega⟩
  refine coprime_of_dvd_of_add_two hodd (Or.inl ?_) (Nat.sub_one_dvd_pow_sub_one x d)
  have := Nat.one_le_pow d x hx1
  omega

theorem coprime_sub_one_self {x : ℕ} (hx1 : 1 ≤ x) : Nat.Coprime (x - 1) x := by
  have h1 := Nat.gcd_dvd_left (x - 1) x
  have h2 := Nat.gcd_dvd_right (x - 1) x
  have h2' : Nat.gcd (x - 1) x ∣ (x - 1) + 1 := by rwa [Nat.sub_add_cancel hx1]
  exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right h1).1 h2')

theorem coprime_add_one_self (x : ℕ) : Nat.Coprime (x + 1) x := by
  have h1 := Nat.gcd_dvd_left (x + 1) x
  have h2 := Nat.gcd_dvd_right (x + 1) x
  exact Nat.eq_one_of_dvd_one ((Nat.dvd_add_right h2).1 h1)

theorem add_one_dvd_pow_two_mul_sub_one (x k : ℕ) : x + 1 ∣ x ^ (2 * k) - 1 := by
  have hsq : x ^ 2 - 1 = (x + 1) * (x - 1) := by
    have := Nat.sq_sub_sq x 1
    simpa using this
  have h := Nat.sub_one_dvd_pow_sub_one (x ^ 2) k
  rw [← pow_mul] at h
  exact (Dvd.intro (x - 1) hsq.symm).trans h

theorem coprime_add_one_pow_even {x : ℕ} (hx : Even x) (hx1 : 1 ≤ x) (k : ℕ) :
    Nat.Coprime (x + 1) (x ^ (2 * k) + 1) := by
  refine coprime_of_dvd_of_add_two hx.add_one (Or.inl ?_) (add_one_dvd_pow_two_mul_sub_one x k)
  have := Nat.one_le_pow (2 * k) x hx1
  omega

theorem coprime_add_one_pow_odd {x : ℕ} (hx : Even x) (hx1 : 1 ≤ x) (k : ℕ) :
    Nat.Coprime (x + 1) (x ^ (2 * k + 1) - 1) := by
  have h := Odd.nat_add_dvd_pow_add_pow x 1 (n := 2 * k + 1) ⟨k, rfl⟩
  rw [one_pow] at h
  refine coprime_of_dvd_of_add_two hx.add_one (Or.inr ?_) h
  have := Nat.one_le_pow (2 * k + 1) x hx1
  omega

theorem coprime_sub_one_ratE6 {x : ℕ} (hx : Even x) (hx1 : 1 ≤ x) :
    Nat.Coprime (x - 1) (ratE6 x) := by
  have hc := coprime_sub_one_pow_add_one hx hx1
  unfold ratE6
  exact ((((((Nat.Coprime.pow_right 36 (coprime_sub_one_self hx1)).mul_right (hc 12)).mul_right
    (hc 9)).mul_right (hc 8)).mul_right (hc 6)).mul_right (hc 5)).mul_right (hc 2)

theorem coprime_add_one_ratTwistedE6 {x : ℕ} (hx : Even x) (hx1 : 1 ≤ x) :
    Nat.Coprime (x + 1) (ratTwistedE6 x) := by
  have he := coprime_add_one_pow_even hx hx1
  have ho := coprime_add_one_pow_odd hx hx1
  unfold ratTwistedE6
  exact ((((((Nat.Coprime.pow_right 36 (coprime_add_one_self x)).mul_right (he 6)).mul_right
    (ho 4)).mul_right (he 4)).mul_right (he 3)).mul_right (ho 2)).mul_right (he 1)

theorem sub_one_pow_six_dvd_numE6 (x : ℕ) : (x - 1) ^ 6 ∣ numE6 x := by
  have h := Nat.sub_one_dvd_pow_sub_one x
  unfold numE6
  have e : (x - 1) ^ 6 = (x - 1) * (x - 1) * (x - 1) * (x - 1) * (x - 1) * (x - 1) := by ring
  rw [e]
  refine mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ?_ (h 9)) (h 8)) (h 6))
    (h 5)) (h 2)
  exact Dvd.dvd.mul_left (h 12) _

theorem sub_one_pow_four_dvd_numTwistedE6 (x : ℕ) : (x - 1) ^ 4 ∣ numTwistedE6 x := by
  have h := Nat.sub_one_dvd_pow_sub_one x
  unfold numTwistedE6
  have e : (x - 1) ^ 4 = (x - 1) * 1 * (x - 1) * (x - 1) * 1 * (x - 1) := by ring
  rw [e]
  refine mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ?_ (one_dvd _)) (h 8))
    (h 6)) (one_dvd _)) (h 2)
  exact Dvd.dvd.mul_left (h 12) _

theorem add_one_pow_six_dvd_numTwistedE6 (x : ℕ) : (x + 1) ^ 6 ∣ numTwistedE6 x := by
  have h := add_one_dvd_pow_two_mul_sub_one x
  have h9 := Odd.nat_add_dvd_pow_add_pow x 1 (n := 9) (by decide)
  have h5 := Odd.nat_add_dvd_pow_add_pow x 1 (n := 5) (by decide)
  rw [one_pow] at h9 h5
  unfold numTwistedE6
  have e : (x + 1) ^ 6 = (x + 1) * (x + 1) * (x + 1) * (x + 1) * (x + 1) * (x + 1) := by ring
  rw [e]
  refine mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul (mul_dvd_mul ?_ h9) (h 4)) (h 3))
    h5) (h 1)
  exact Dvd.dvd.mul_left (h 6) _

theorem ordE6_mul_gcd (x : ℕ) : ordE6 x * Nat.gcd 3 (x - 1) = numE6 x := by
  refine Nat.div_mul_cancel ((Nat.gcd_dvd_right 3 (x - 1)).trans ?_)
  exact Dvd.dvd.mul_left (Nat.sub_one_dvd_pow_sub_one x 2) _

theorem ordTwistedE6_mul_gcd (x : ℕ) : ordTwistedE6 x * Nat.gcd 3 (x + 1) = numTwistedE6 x := by
  refine Nat.div_mul_cancel ((Nat.gcd_dvd_right 3 (x + 1)).trans ?_)
  have h9 := Odd.nat_add_dvd_pow_add_pow x 1 (n := 9) (by decide)
  rw [one_pow] at h9
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (Dvd.dvd.mul_left h9 _) _) _) _) _

theorem ordE6_dvd_numE6 (x : ℕ) : ordE6 x ∣ numE6 x :=
  Dvd.intro _ (ordE6_mul_gcd x)

theorem ordE6_pos {x : ℕ} (hx : 2 ≤ x) : 0 < ordE6 x := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have h1 := ordE6_mul_gcd x
  rw [h, zero_mul] at h1
  have hk : ∀ k, 0 < k → 0 < x ^ k - 1 := fun k hk => by
    have : 2 ≤ x ^ k := le_trans hx (Nat.le_self_pow (by omega) x)
    omega
  have : 0 < numE6 x := by
    unfold numE6
    have := hk 12 (by norm_num)
    have := hk 9 (by norm_num)
    have := hk 8 (by norm_num)
    have := hk 6 (by norm_num)
    have := hk 5 (by norm_num)
    have := hk 2 (by norm_num)
    positivity
  omega

theorem ordTwistedE6_pos {x : ℕ} (hx : 2 ≤ x) : 0 < ordTwistedE6 x := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have h1 := ordTwistedE6_mul_gcd x
  rw [h, zero_mul] at h1
  have hk : ∀ k, 0 < k → 0 < x ^ k - 1 := fun k hk => by
    have : 2 ≤ x ^ k := le_trans hx (Nat.le_self_pow (by omega) x)
    omega
  have : 0 < numTwistedE6 x := by
    unfold numTwistedE6
    have := hk 12 (by norm_num)
    have := hk 8 (by norm_num)
    have := hk 6 (by norm_num)
    have := hk 2 (by norm_num)
    positivity
  omega

theorem gcd_three_le (y : ℕ) : Nat.gcd 3 y ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)

theorem not_mul_dvd_ordE6_sq {e : ℕ} (he : 1 ≤ e) {Y Z : ℕ}
    (hY : Y = ordE6 (2 ^ e) ∨ Y = ordTwistedE6 (2 ^ e))
    (hZ : Z = ordE6 (2 ^ e) ∨ Z = ordTwistedE6 (2 ^ e)) : ¬ Y * Z ∣ ordE6 ((2 ^ e) ^ 2) := by
  set x := 2 ^ e with hxdef
  have hx2 : 2 ≤ x := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hx1 : 1 ≤ x := by omega
  have hxe : Even x := by rw [hxdef]; exact (Nat.even_pow' (by omega)).2 even_two
  have hsq : ordE6 (x ^ 2) ∣ numE6 (x ^ 2) := ordE6_dvd_numE6 _
  have hE : ∀ W : ℕ, (W = ordE6 x ∨ W = ordTwistedE6 x) → ¬ ordE6 x * W ∣ ordE6 (x ^ 2) := by
    intro W hW hdvd
    have h1 : ordE6 x * W ∣ ordE6 x * (Nat.gcd 3 (x - 1) * ratE6 x) := by
      rw [← mul_assoc, ordE6_mul_gcd, ← numE6_sq hx1]
      exact hdvd.trans hsq
    have h2 : W ∣ Nat.gcd 3 (x - 1) * ratE6 x := Nat.dvd_of_mul_dvd_mul_left (ordE6_pos hx2) h1
    obtain ⟨c, hc0, hc, hcW⟩ : ∃ c, 0 < c ∧ c ≤ 3 ∧ (x - 1) ^ 4 ∣ W * c := by
      rcases hW with rfl | rfl
      · refine ⟨Nat.gcd 3 (x - 1), Nat.gcd_pos_of_pos_left _ (by norm_num), gcd_three_le _, ?_⟩
        rw [ordE6_mul_gcd]
        exact (pow_dvd_pow (x - 1) (by norm_num : 4 ≤ 6)).trans (sub_one_pow_six_dvd_numE6 x)
      · refine ⟨Nat.gcd 3 (x + 1), Nat.gcd_pos_of_pos_left _ (by norm_num), gcd_three_le _, ?_⟩
        rw [ordTwistedE6_mul_gcd]
        exact sub_one_pow_four_dvd_numTwistedE6 x
    have h3 : (x - 1) ^ 4 ∣ (c * Nat.gcd 3 (x - 1)) * ratE6 x := by
      refine hcW.trans ?_
      rw [mul_comm W c, mul_assoc]
      exact mul_dvd_mul_left c h2
    have h4 : (x - 1) ^ 4 ∣ c * Nat.gcd 3 (x - 1) :=
      ((coprime_sub_one_ratE6 hxe hx1).pow_left 4).dvd_of_dvd_mul_right h3
    have h5 : c * Nat.gcd 3 (x - 1) ≤ 9 := by
      have := gcd_three_le (x - 1)
      calc c * Nat.gcd 3 (x - 1) ≤ 3 * 3 := Nat.mul_le_mul hc this
        _ = 9 := by norm_num
    have h6 : 0 < c * Nat.gcd 3 (x - 1) := Nat.mul_pos hc0 (Nat.gcd_pos_of_pos_left _ (by norm_num))
    have h7 : (x - 1) ^ 4 ≤ 9 := (Nat.le_of_dvd h6 h4).trans h5
    have h8 : x = 2 := by
      by_contra hne
      have : 2 ≤ x - 1 := by omega
      have := Nat.pow_le_pow_left this 4
      omega
    have he1 : e = 1 := by
      have h9 : 2 ^ e = 2 ^ 1 := by rw [← hxdef, h8]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h9
    subst he1
    rcases hW with rfl | rfl
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
  rcases hY with rfl | rfl
  · exact hE Z hZ
  rcases hZ with rfl | rfl
  · rw [mul_comm]
    exact hE _ (Or.inr rfl)
  intro hdvd
  have h1 : ordTwistedE6 x * ordTwistedE6 x ∣
      ordTwistedE6 x * (Nat.gcd 3 (x + 1) * ratTwistedE6 x) := by
    rw [← mul_assoc, ordTwistedE6_mul_gcd, ← numE6_sq' hx1]
    exact hdvd.trans hsq
  have h2 : ordTwistedE6 x ∣ Nat.gcd 3 (x + 1) * ratTwistedE6 x :=
    Nat.dvd_of_mul_dvd_mul_left (ordTwistedE6_pos hx2) h1
  have h3 : (x + 1) ^ 6 ∣ (Nat.gcd 3 (x + 1) * Nat.gcd 3 (x + 1)) * ratTwistedE6 x := by
    refine (add_one_pow_six_dvd_numTwistedE6 x).trans ?_
    rw [← ordTwistedE6_mul_gcd, mul_comm (ordTwistedE6 x), mul_assoc]
    exact mul_dvd_mul_left _ h2
  have h4 : (x + 1) ^ 6 ∣ Nat.gcd 3 (x + 1) * Nat.gcd 3 (x + 1) :=
    ((coprime_add_one_ratTwistedE6 hxe hx1).pow_left 6).dvd_of_dvd_mul_right h3
  have h5 : Nat.gcd 3 (x + 1) * Nat.gcd 3 (x + 1) ≤ 9 := by
    have := gcd_three_le (x + 1)
    calc Nat.gcd 3 (x + 1) * Nat.gcd 3 (x + 1) ≤ 3 * 3 := Nat.mul_le_mul this this
      _ = 9 := by norm_num
  have h6 : 0 < Nat.gcd 3 (x + 1) * Nat.gcd 3 (x + 1) :=
    Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (by norm_num)) (Nat.gcd_pos_of_pos_left _ (by norm_num))
  have h7 : (x + 1) ^ 6 ≤ 9 := (Nat.le_of_dvd h6 h4).trans h5
  have : 3 ^ 6 ≤ (x + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  omega

end CFSG.SeitzReduction.E6Pilot
