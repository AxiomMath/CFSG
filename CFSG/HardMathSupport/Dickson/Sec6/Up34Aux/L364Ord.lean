module

public import Mathlib
public import CFSG.Open.StatedDefs
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Up34Ord

open CFSG.Open

theorem psl3_sixtyFour_order :
    64 ^ 3 * ((64 ^ 2 - 1) * (64 ^ 3 - 1)) / Nat.gcd 3 (64 - 1) = 93801727918080 := by
  norm_num

theorem psl_arith (q : ℕ)
    (h : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) = 93801727918080) :
    q = 64 := by
  by_cases hq : 65 ≤ q
  · exfalso
    have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hg0 : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : 4225 ≤ q ^ 2 := by nlinarith
    have h2 : 274625 ≤ q ^ 3 := by nlinarith
    have h3 : 274625 * (4224 * 274624) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul h2 (Nat.mul_le_mul (by omega) (by omega))
    have h4 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 ≤
        q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) :=
      Nat.div_le_div_left hg (by omega)
    have h5 : 93801727918080 < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / 3 := by
      rw [Nat.lt_div_iff_mul_lt (by norm_num)]
      omega
    omega
  · push Not at hq
    interval_cases q <;> first | rfl | (exfalso; norm_num at h)

theorem psu_arith (q : ℕ) :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) ≠ 93801727918080 := by
  intro h
  by_cases hq : 65 ≤ q
  · have hg : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hg0 : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : 4225 ≤ q ^ 2 := by nlinarith
    have h2 : 274625 ≤ q ^ 3 := by nlinarith
    have h3 : 274625 * (4224 * 274626) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      Nat.mul_le_mul h2 (Nat.mul_le_mul (by omega) (by omega))
    have h4 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3 ≤
        q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) :=
      Nat.div_le_div_left hg (by omega)
    have h5 : 93801727918080 < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / 3 := by
      rw [Nat.lt_div_iff_mul_lt (by norm_num)]
      omega
    omega
  · push Not at hq
    interval_cases q <;> norm_num at h

theorem card_psl3 {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) /
        Nat.gcd 3 (Nat.card K - 1) := by
  have e := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3)
    (by norm_num : 1 ≤ 3)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at e
  exact e

theorem card_eq_sixtyFour_of_equiv {K K₀ : Type} [Field K] [Finite K] [Field K₀] [Finite K₀]
    (h64 : Nat.card K₀ = 64)
    (e : StatedProj (StatedSL 3 K) ≃* StatedProj (StatedSL 3 K₀)) : Nat.card K = 64 := by
  have h1 : Nat.card (StatedProj (StatedSL 3 K)) = Nat.card (StatedProj (StatedSL 3 K₀)) :=
    Nat.card_congr e.toEquiv
  rw [card_psl3, card_psl3, h64] at h1
  exact psl_arith _ (h1.trans psl3_sixtyFour_order)

theorem card_psu3_ne {K K₀ : Type} [Field K] [Finite K] [Field K₀] [Finite K₀]
    (h64 : Nat.card K₀ = 64) {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Nat.card (StatedProj (StatedSU 3 q K)) ≠ Nat.card (StatedProj (StatedSL 3 K₀)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hpc, n, hp, hn⟩ := FiniteField.card' (K := K)
  have hqn : q ^ 2 = p ^ (n : ℕ) := by rw [← hK, Nat.card_eq_fintype_card, hn]
  have hqd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hqn]; ring⟩
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hqd
  have hq1 : q ≠ 1 := by
    rintro rfl
    have h1 := Finite.one_lt_card (α := K)
    rw [hK] at h1
    simp at h1
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exact absurd (by simpa [h0] using hf) hq1
    · exact h0
  subst hf
  intro h
  have e := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) hp hf1 hK
    (by norm_num : 2 ≤ 3)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at e
  have h' : Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) =
      Nat.card (StatedProj (StatedSL 3 K₀)) := h
  rw [e, card_psl3, h64, psl3_sixtyFour_order] at h'
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have h2 : (((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (p ^ f) ^ 2 - 1 := by
    have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [show ((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub this]; ring]
    exact Int.toNat_natCast _
  have h3 : (((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (p ^ f) ^ 3 + 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [h2, h3] at h'
  exact psu_arith (p ^ f) (by simpa using h')

end CFSG.HardMathSupport.Dickson.Sec6.Up34Ord
