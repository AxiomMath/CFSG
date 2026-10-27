module

public import CFSG.Open.StatedAPI
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowBasic

public section

namespace CFSG.CGT.Stroth77.L4Sylow

open CFSG.Open

private theorem factorization_two_pow_mul_odd {k w : ℕ} (hw : Odd w) :
    (2 ^ k * w).factorization 2 = k := by
  rw [Nat.factorization_mul (pow_ne_zero k two_ne_zero) hw.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hw.not_two_dvd_nat, add_zero]

theorem exists_odd_q_sub_one {q : ℕ} (hq1 : 1 < q) (hq : q % 4 = 1) :
    ∃ u, Odd u ∧ q - 1 = 2 ^ (q - 1).factorization 2 * u ∧ 2 ≤ (q - 1).factorization 2 := by
  obtain ⟨u, hu, hqu⟩ :=
    CFSG.BrauerLinearThree.exists_odd_eq_two_pow_factorization_mul (n := q - 1) (by omega)
  refine ⟨u, hu, hqu, ?_⟩
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)]
  exact Nat.dvd_of_mod_eq_zero (by omega)

theorem card_statedSL_four_mul (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSL 4 K) * (Nat.card K - 1) =
      ∏ i : Fin 4, (Nat.card K ^ 4 - Nat.card K ^ (i : ℕ)) := by
  let := Fintype.ofFinite K
  rw [StatedAPI.card_statedSL, ← Nat.card_units, Matrix.card_SL_mul_card_units,
    Matrix.card_GL_field, Nat.card_eq_fintype_card]

theorem factorization_card_statedSL_four (K : Type) [Field K] [Finite K]
    (hq : Nat.card K % 4 = 1) :
    (Nat.card (StatedSL 4 K)).factorization 2 = 3 * (Nat.card K - 1).factorization 2 + 3 := by
  set q := Nat.card K with hqdef
  have hq2 : 1 < q := Finite.one_lt_card
  obtain ⟨u, hu, hqu, hn⟩ := exists_odd_q_sub_one hq2 hq
  set n := (q - 1).factorization 2
  have hq1 : 1 ≤ q := by omega
  have hprod : ∏ i : Fin 4, (q ^ 4 - q ^ (i : ℕ)) =
      (q ^ 6 * (q - 1) ^ 3 * (q + 1) ^ 2 * (q ^ 2 + 1) * (q ^ 2 + q + 1)) * (q - 1) := by
    rw [Fin.prod_univ_four]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [e3]
    have h0 : q ^ 0 ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
    have h1 : q ^ 1 ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
    have h2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
    have h3 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
    zify [h0, h1, h2, h3, hq1]
    ring
  have hcard : Nat.card (StatedSL 4 K) =
      q ^ 6 * (q - 1) ^ 3 * (q + 1) ^ 2 * (q ^ 2 + 1) * (q ^ 2 + q + 1) :=
    Nat.eq_of_mul_eq_mul_right (by omega) ((card_statedSL_four_mul K).trans hprod)
  have hqodd : Odd q := Nat.odd_iff.2 (by omega)
  obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 1 := ⟨q / 4, by omega⟩
  have hadd : q + 1 = 2 * (2 * t + 1) := by omega
  have hsq : q ^ 2 + 1 = 2 * (8 * t ^ 2 + 4 * t + 1) := by rw [ht]; ring
  have hb : Odd (8 * t ^ 2 + 4 * t + 1) := ⟨4 * t ^ 2 + 2 * t, by ring⟩
  have hR : Odd (q ^ 2 + q + 1) := ((hqodd.pow.add_odd hqodd).add_one)
  have hform : Nat.card (StatedSL 4 K) = 2 ^ (3 * n + 3) *
      (q ^ 6 * u ^ 3 * (2 * t + 1) ^ 2 * (8 * t ^ 2 + 4 * t + 1) * (q ^ 2 + q + 1)) := by
    rw [hcard, hqu, hadd, hsq]
    ring
  rw [hform, factorization_two_pow_mul_odd]
  exact (((hqodd.pow.mul hu.pow).mul (odd_two_mul_add_one t).pow).mul hb).mul hR

end CFSG.CGT.Stroth77.L4Sylow
