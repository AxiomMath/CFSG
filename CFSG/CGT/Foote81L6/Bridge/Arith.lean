module

public import CFSG.Open.StatedAPI
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowBasic

public section

namespace CFSG.CGT.Foote81L6.Bridge

open CFSG.Open

private theorem factorization_two_pow_mul_odd {k w : ℕ} (hw : Odd w) :
    (2 ^ k * w).factorization 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero k two_ne_zero) hw.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hw.not_two_dvd_nat, add_zero]

section Arith

variable {q : ℕ}

theorem exists_odd_q_add_one (hq : q % 4 = 3) :
    ∃ u, Odd u ∧ q + 1 = 2 ^ ((q ^ 2 - 1).factorization 2 - 1) * u ∧
      3 ≤ (q ^ 2 - 1).factorization 2 := by
  obtain ⟨u, hu, hqu⟩ :=
    CFSG.BrauerLinearThree.exists_odd_eq_two_pow_factorization_mul (n := q + 1) (by omega)
  set m := (q + 1).factorization 2 with hm
  have hm2 : 2 ≤ m := by
    rw [hm, ← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have ha : Odd ((q - 1) / 2) := ⟨(q - 3) / 4, by omega⟩
  have hsq : q ^ 2 - 1 = 2 ^ (m + 1) * ((q - 1) / 2 * u) := by
    have e1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have hq1 : 1 ≤ q := by omega
      have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [hq1, hq2]
      ring
    have e2 : q - 1 = 2 * ((q - 1) / 2) := by omega
    rw [e1, hqu]
    conv_lhs => rw [e2]
    ring
  have hv : (q ^ 2 - 1).factorization 2 = m + 1 := by
    rw [hsq, factorization_two_pow_mul_odd (ha.mul hu)]
  refine ⟨u, hu, ?_, by omega⟩
  rw [hv, Nat.add_sub_cancel]
  exact hqu

theorem mod_two_pow_v2 (hq : q % 4 = 3) :
    q % 2 ^ (q ^ 2 - 1).factorization 2 = 2 ^ ((q ^ 2 - 1).factorization 2 - 1) - 1 := by
  obtain ⟨u, ⟨v, rfl⟩, hqu, hn⟩ := exists_odd_q_add_one hq
  set n := (q ^ 2 - 1).factorization 2
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ', show n - 1 + 1 = n by omega]
  have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  have hlt : 2 ^ (n - 1) - 1 < 2 ^ n := by omega
  have hq' : q = (2 ^ (n - 1) - 1) + 2 ^ n * v := by
    have : q + 1 = 2 ^ n * v + 2 ^ (n - 1) := by rw [hqu, h2n]; ring
    omega
  rw [hq', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end Arith

theorem card_statedSL_six_mul (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSL 6 K) * (Nat.card K - 1) =
      ∏ i : Fin 6, (Nat.card K ^ 6 - Nat.card K ^ (i : ℕ)) := by
  let := Fintype.ofFinite K
  rw [StatedAPI.card_statedSL, ← Nat.card_units, Matrix.card_SL_mul_card_units,
    Matrix.card_GL_field, Nat.card_eq_fintype_card]

theorem factorization_card_statedSL_six (K : Type) [Field K] [Finite K]
    (hq : Nat.card K % 4 = 3) :
    (Nat.card (StatedSL 6 K)).factorization 2 =
      3 * (Nat.card K ^ 2 - 1).factorization 2 + 3 := by
  set q := Nat.card K with hqdef
  obtain ⟨u, hu, hqu, hn⟩ := exists_odd_q_add_one hq
  set n := (q ^ 2 - 1).factorization 2
  have hq1 : 1 ≤ q := by omega
  have hprod : ∏ i : Fin 6, (q ^ 6 - q ^ (i : ℕ)) =
      (q ^ 15 * (q - 1) ^ 5 * (q + 1) ^ 3 * (q ^ 2 + 1) *
        ((q ^ 4 + q ^ 2 + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * (q ^ 2 + q + 1))) * (q - 1) := by
    rw [Fin.prod_univ_six]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
    have e3 : ((3 : Fin 6) : ℕ) = 3 := rfl
    have e4 : ((4 : Fin 6) : ℕ) = 4 := rfl
    have e5 : ((5 : Fin 6) : ℕ) = 5 := rfl
    rw [e3, e4, e5]
    have h0 : q ^ 0 ≤ q ^ 6 := Nat.pow_le_pow_right hq1 (by norm_num)
    have h1 : q ^ 1 ≤ q ^ 6 := Nat.pow_le_pow_right hq1 (by norm_num)
    have h2 : q ^ 2 ≤ q ^ 6 := Nat.pow_le_pow_right hq1 (by norm_num)
    have h3 : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right hq1 (by norm_num)
    have h4 : q ^ 4 ≤ q ^ 6 := Nat.pow_le_pow_right hq1 (by norm_num)
    have h5 : q ^ 5 ≤ q ^ 6 := Nat.pow_le_pow_right hq1 (by norm_num)
    zify [h0, h1, h2, h3, h4, h5, hq1]
    ring
  have hcard : Nat.card (StatedSL 6 K) =
      q ^ 15 * (q - 1) ^ 5 * (q + 1) ^ 3 * (q ^ 2 + 1) *
        ((q ^ 4 + q ^ 2 + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * (q ^ 2 + q + 1)) :=
    Nat.eq_of_mul_eq_mul_right (by omega) ((card_statedSL_six_mul K).trans hprod)
  have hqodd : Odd q := Nat.odd_iff.2 (by omega)
  obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 3 := ⟨q / 4, by omega⟩
  have hsub : q - 1 = 2 * (2 * t + 1) := by omega
  have hsq : q ^ 2 + 1 = 2 * (8 * t ^ 2 + 12 * t + 5) := by rw [ht]; ring
  have hb : Odd (8 * t ^ 2 + 12 * t + 5) := ⟨4 * t ^ 2 + 6 * t + 2, by ring⟩
  have hR : Odd ((q ^ 4 + q ^ 2 + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * (q ^ 2 + q + 1)) := by
    have hq2 := hqodd.pow (n := 2)
    have hq3 := hqodd.pow (n := 3)
    have hq4 := hqodd.pow (n := 4)
    refine (((hq4.add_odd hq2).add_one).mul ?_).mul ((hq2.add_odd hqodd).add_one)
    exact (((hq4.add_odd hq3).add_odd hq2).add_odd hqodd).add_one
  have hform : Nat.card (StatedSL 6 K) = 2 ^ (3 * n + 3) *
      (q ^ 15 * (2 * t + 1) ^ 5 * u ^ 3 * (8 * t ^ 2 + 12 * t + 5) *
        ((q ^ 4 + q ^ 2 + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * (q ^ 2 + q + 1))) := by
    rw [hcard, hsub, hqu, hsq, show 3 * n + 3 = 5 + 3 * (n - 1) + 1 by omega]
    ring
  rw [hform, factorization_two_pow_mul_odd]
  exact ((((hqodd.pow.mul (odd_two_mul_add_one t).pow).mul hu.pow).mul hb).mul hR)

end CFSG.CGT.Foote81L6.Bridge
