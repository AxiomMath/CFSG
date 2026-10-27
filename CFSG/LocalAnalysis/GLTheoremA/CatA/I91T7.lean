module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T5

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem two_pow_eq_of_odd {a b m n : ℕ} (hm : Odd m) (hn : Odd n) (h : 2 ^ a * m = 2 ^ b * n) : a = b := by
  have key : ∀ c l : ℕ, Odd l → (2 ^ c * l).factorization 2 = c := by
    intro c l hl
    have hl0 : l ≠ 0 := hl.pos.ne'
    have hnd : ¬ 2 ∣ l := by
      rw [Nat.two_dvd_ne_zero]
      exact Nat.odd_iff.1 hl
    rw [Nat.factorization_mul (by positivity) hl0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hnd]
    simp
  have := congrArg (fun x => Nat.factorization x 2) h
  rw [key a m hm, key b n hn] at this
  exact this

theorem orderA_two_eq_mul {R : ℕ} (h3 : R % 3 = 1) :
    ∃ Y : ℕ, orderA 2 R = R ^ 3 * Y ∧ (R ^ 2 - 1) * (R ^ 3 - 1) = 3 * Y := by
  obtain ⟨c, rfl⟩ : ∃ c, R = 3 * c + 1 := ⟨R / 3, by omega⟩
  have e1 : (3 * c + 1) ^ 2 - 1 = 3 * (3 * c ^ 2 + 2 * c) :=
    Nat.sub_eq_of_eq_add (by ring)
  have hdvd : 3 ∣ ((3 * c + 1) ^ 2 - 1) * ((3 * c + 1) ^ 3 - 1) := by
    rw [e1]
    exact Dvd.dvd.mul_right (dvd_mul_right 3 _) _
  obtain ⟨Y, hY⟩ := hdvd
  refine ⟨Y, ?_, hY⟩
  unfold orderA
  have hgcd : Nat.gcd (2 + 1) (3 * c + 1 - 1) = 3 := by
    rw [show 3 * c + 1 - 1 = 3 * c from by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 3 c)
  have hprod : (∏ i ∈ Finset.Icc 2 (2 + 1), ((3 * c + 1) ^ i - 1)) =
      ((3 * c + 1) ^ 2 - 1) * ((3 * c + 1) ^ 3 - 1) := by
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} from by decide]
    simp [Finset.prod_insert]
  rw [hgcd, hprod, hY, show 2 * (2 + 1) / 2 = 3 from rfl, show 3 * Y = 3 * Y from rfl]
  rw [show (3 * c + 1) ^ 3 * (3 * Y) = 3 * ((3 * c + 1) ^ 3 * Y) by ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

theorem poly_ne_of_four_le {a : ℤ} (ha : 4 ≤ a) :
    (a + 1) * (a ^ 2 + 1) * (a ^ 3 + 1) ≠ 3 * (a ^ 4 + a ^ 2 + 1) := by
  intro h
  have h2 : 16 ≤ a ^ 2 := by nlinarith
  have h6 : 16 * a ^ 4 ≤ a ^ 6 := by
    have e : a ^ 6 = a ^ 4 * a ^ 2 := by ring
    rw [e]
    nlinarith [pow_nonneg (by linarith : (0:ℤ) ≤ a) 4]
  have h3 : a ^ 2 ≤ a ^ 3 := by
    have e : a ^ 3 = a ^ 2 * a := by ring
    rw [e]
    nlinarith [pow_nonneg (by linarith : (0:ℤ) ≤ a) 2]
  have h5 : 0 ≤ a ^ 5 := pow_nonneg (by linarith) 5
  have h4 : 0 ≤ a ^ 4 := pow_nonneg (by linarith) 4
  nlinarith [h, h6, h3, h5, h4, ha]

theorem final_contra {a : ℕ} (ha : 4 ≤ a)
    (hEq : (a ^ 4 - 1) * (a ^ 6 - 1) = 3 * ((a ^ 4 + a ^ 2 + 1) * (a ^ 3 - 1) * (a - 1))) : False := by
  have h1 : 1 ≤ a := by omega
  have h3 : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ h1
  have h4 : 1 ≤ a ^ 4 := Nat.one_le_pow _ _ h1
  have h6 : 1 ≤ a ^ 6 := Nat.one_le_pow _ _ h1
  zify [h1, h3, h4, h6] at hEq
  have ha' : (4 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have key : ((a : ℤ) - 1) * ((a : ℤ) ^ 3 - 1) *
      (((a : ℤ) + 1) * ((a : ℤ) ^ 2 + 1) * ((a : ℤ) ^ 3 + 1) - 3 * ((a : ℤ) ^ 4 + (a : ℤ) ^ 2 + 1)) = 0 := by
    linear_combination hEq
  have hne : ((a : ℤ) - 1) * ((a : ℤ) ^ 3 - 1) ≠ 0 := by
    apply mul_ne_zero <;> nlinarith
  rcases mul_eq_zero.1 key with h | h
  · exact hne h
  · exact poly_ne_of_four_le ha' (by linarith)

theorem td4_even_ne_A2 {f k : ℕ} (hf : 1 ≤ f) (hk : 2 ≤ k) (hke : Even k) :
    orderTrialityD4 (2 ^ f) ≠ orderA 2 (2 ^ k) := by
  intro heq
  have hR3 : (2 : ℕ) ^ k % 3 = 1 := two_pow_mod_three_even hke
  obtain ⟨Y, hYA, hXY⟩ := orderA_two_eq_mul hR3
  rw [hYA] at heq
  unfold orderTrialityD4 at heq
  have hQ2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hR2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have hQe : Even (2 ^ f) := even_iff_two_dvd.2 hQ2
  have hRe : Even (2 ^ k) := even_iff_two_dvd.2 hR2
  have hZodd : Odd (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
    have hA : Odd ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) :=
      Even.add_one ((Nat.even_pow.2 ⟨hQe, by norm_num⟩).add (Nat.even_pow.2 ⟨hQe, by norm_num⟩))
    have hB : Odd ((2 ^ f) ^ 6 - 1) := by
      have h6 : 1 ≤ (2 ^ f) ^ 6 := Nat.one_le_pow _ _ (by positivity)
      obtain ⟨r, hr⟩ := (Nat.even_pow.2 ⟨hQe, by norm_num⟩ : Even ((2 ^ f) ^ 6))
      rw [Nat.odd_iff]
      omega
    have hC : Odd ((2 ^ f) ^ 2 - 1) := by
      have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      obtain ⟨r, hr⟩ := (Nat.even_pow.2 ⟨hQe, by norm_num⟩ : Even ((2 ^ f) ^ 2))
      rw [Nat.odd_iff]
      omega
    exact (hA.mul hB).mul hC
  have hYodd : Odd Y := by
    have hX : Odd ((2 ^ k) ^ 2 - 1) := by
      have h2 : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      obtain ⟨r, hr⟩ := (Nat.even_pow.2 ⟨hRe, by norm_num⟩ : Even ((2 ^ k) ^ 2))
      rw [Nat.odd_iff]
      omega
    have hX' : Odd ((2 ^ k) ^ 3 - 1) := by
      have h3 : 1 ≤ (2 ^ k) ^ 3 := Nat.one_le_pow _ _ (by positivity)
      obtain ⟨r, hr⟩ := (Nat.even_pow.2 ⟨hRe, by norm_num⟩ : Even ((2 ^ k) ^ 3))
      rw [Nat.odd_iff]
      omega
    have hodd3Y : Odd (3 * Y) := by
      rw [← hXY]
      exact hX.mul hX'
    exact (Nat.odd_mul.1 hodd3Y).2
  have hZdef : (2 ^ f) ^ 12 * ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)
      = 2 ^ (f * 12) * (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
    rw [← pow_mul]
    ring
  have hR' : (2 ^ k) ^ 3 * Y = 2 ^ (k * 3) * Y := by rw [← pow_mul]
  rw [hZdef, hR'] at heq
  have hfk : f * 12 = k * 3 := two_pow_eq_of_odd hZodd hYodd heq
  have hZY : (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) = Y := by
    rw [hfk] at heq
    exact Nat.eq_of_mul_eq_mul_left (by positivity) heq
  have hk4 : (2 : ℕ) ^ k = ((2 ^ f) ^ 2) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = (2 ^ f) ^ 2 := ⟨_, rfl⟩
  have ha4 : 4 ≤ a := by
    rw [ha]
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    nlinarith
  have hQ8 : (2 ^ f) ^ 8 = a ^ 4 := by rw [ha]; ring
  have hQ4 : (2 ^ f) ^ 4 = a ^ 2 := by rw [ha]; ring
  have hQ6 : (2 ^ f) ^ 6 = a ^ 3 := by rw [ha]; ring
  have hQ2 : (2 ^ f) ^ 2 = a := ha.symm
  rw [hQ8, hQ4, hQ6, hQ2] at hZY
  have hk4' : (2 : ℕ) ^ k = a ^ 2 := by rw [hk4, ← ha]
  have hXY2 : (a ^ 4 - 1) * (a ^ 6 - 1) = 3 * Y := by
    rw [hk4'] at hXY
    rw [show (a ^ 2) ^ 2 = a ^ 4 by ring, show (a ^ 2) ^ 3 = a ^ 6 by ring] at hXY
    exact hXY
  have hEq : (a ^ 4 - 1) * (a ^ 6 - 1) = 3 * ((a ^ 4 + a ^ 2 + 1) * (a ^ 3 - 1) * (a - 1)) := by
    rw [hXY2, ← hZY]
  exact final_contra ha4 hEq

end I91T

end CFSG.LocalAnalysis.GLTheoremA
