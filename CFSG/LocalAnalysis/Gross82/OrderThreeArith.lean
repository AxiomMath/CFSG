module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.Permutation.SylowTwoNormalizer.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.Gross82.OrderThree

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open Finset

theorem false_of_card_fixedSubgroup_dvd (hLie : LieOrderFormulasInput) {K : Type} [Group K]
    [Finite K] {t : StatedLieTag} {n ℓ f : ℕ} (hadm : StatedLieAdmissible t n ℓ f)
    (hmodel : CFSG.Blueprint.LieModel K t n ℓ f) {α : MulAut K} (P : Sylow 3 K)
    (hfix : ∀ x ∈ (P : Subgroup K), α x = x) {s a : ℕ} (hs : ℓ ^ f = s ^ 3) (ha : a ≠ 0)
    (hC : Nat.card (fixedSubgroup α) ∣ a)
    (hlt : padicValNat 3 a + padicValNat 3 (lieOrderDivisor t n (s ^ 3)) <
      padicValNat 3 (lieOrderNumerator t n (s ^ 3))) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hcard, -⟩ := hLie K t n ℓ f hadm hmodel
  rw [hs] at hcard
  have hPdvd : 3 ^ (Nat.card K).factorization 3 ∣ a := by
    rw [← P.card_eq_multiplicity]
    exact (Subgroup.card_dvd_of_le fun x hx => hfix x hx).trans hC
  have hle : padicValNat 3 (Nat.card K) ≤ padicValNat 3 a := by
    rw [← Nat.factorization_def (Nat.card K) Nat.prime_three]
    exact (padicValNat_dvd_iff_le ha).mp hPdvd
  have hK0 : Nat.card K ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  by_cases hD0 : lieOrderDivisor t n (s ^ 3) = 0
  · have hN0 : lieOrderNumerator t n (s ^ 3) = 0 := by rw [← hcard, hD0, mul_zero]
    rw [hN0, padicValNat.zero] at hlt
    omega
  · have hN : padicValNat 3 (lieOrderNumerator t n (s ^ 3)) =
        padicValNat 3 (Nat.card K) + padicValNat 3 (lieOrderDivisor t n (s ^ 3)) := by
      rw [← hcard, padicValNat.mul hK0 hD0]
    rw [hN] at hlt
    omega

private lemma pow_mod_three_of_mod_two_even {s i : ℕ} (hs : s % 3 = 2) (hi : Even i) :
    s ^ i % 3 = 1 := by
  obtain ⟨j, hj⟩ := even_iff_exists_two_mul.mp hi
  subst hj
  rw [pow_mul, Nat.pow_mod, show s ^ 2 % 3 = 1 by rw [Nat.pow_mod, hs]]
  norm_num

private lemma pow_mod_three_of_mod_two_odd {s i : ℕ} (hs : s % 3 = 2) (hi : Odd i) :
    s ^ i % 3 = 2 := by
  obtain ⟨j, hj⟩ := hi
  have h2 : i = 2 * j + 1 := by omega
  rw [h2, pow_succ, Nat.mul_mod, pow_mul, Nat.pow_mod,
    show s ^ 2 % 3 = 1 by rw [Nat.pow_mod, hs]]
  norm_num [hs]

private lemma padicValNat_three_sq_sub_one_of_not_dvd_add {x : ℕ} (hx : 2 ≤ x)
    (h : ¬ 3 ∣ x + 1) : padicValNat 3 (x ^ 2 - 1) = padicValNat 3 (x - 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsq : x ^ 2 - 1 = (x - 1) * (x + 1) := by
    rw [Nat.mul_comm]
    simpa using Nat.sq_sub_sq x 1
  rw [hsq, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd h, add_zero]

private lemma padicValNat_three_sq_sub_one_of_not_dvd_sub {x : ℕ} (hx : 2 ≤ x)
    (h : ¬ 3 ∣ x - 1) : padicValNat 3 (x ^ 2 - 1) = padicValNat 3 (x + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsq : x ^ 2 - 1 = (x - 1) * (x + 1) := by
    rw [Nat.mul_comm]
    simpa using Nat.sq_sub_sq x 1
  rw [hsq, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd h, zero_add]

private lemma padicValNat_three_pow_two_mul_sub_one {s i : ℕ} (hs : 2 ≤ s) (hs3 : s % 3 = 2)
    (hi : 2 ≤ i) :
    padicValNat 3 ((s ^ 2) ^ i - 1) =
      padicValNat 3 (if Even i then s ^ i - 1 else s ^ i + 1) := by
  have hp : (s ^ 2) ^ i = (s ^ i) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hsi : 2 ≤ s ^ i := by
    have h0 : i ≠ 0 := by omega
    have h1 : 1 < s ^ i := Nat.one_lt_pow h0 (by omega)
    omega
  rw [hp]
  by_cases he : Even i
  · rw [if_pos he]
    exact padicValNat_three_sq_sub_one_of_not_dvd_add hsi
      (by have h := pow_mod_three_of_mod_two_even hs3 he; omega)
  · rw [if_neg he]
    exact padicValNat_three_sq_sub_one_of_not_dvd_sub hsi
      (by have h := pow_mod_three_of_mod_two_odd hs3 (Nat.not_even_iff_odd.mp he); omega)

theorem padicValNat_three_lieOrder_psl_sq_eq_psu {s n : ℕ} (hs : 2 ≤ s) (h3 : 3 ∣ s + 1) :
    padicValNat 3 (lieOrderNumerator .PSL n (s ^ 2)) =
      padicValNat 3 (lieOrderNumerator .PSU n s) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : s % 3 = 2 := by omega
  have hs0 : s ≠ 0 := by omega
  have hs20 : s ^ 2 ≠ 0 := pow_ne_zero _ hs0
  have hne1 : ∀ i ∈ Icc 2 n, (s ^ 2) ^ i - 1 ≠ 0 := by
    intro i hi
    have hi0 : i ≠ 0 := by have := (mem_Icc.mp hi).1; omega
    have h2 : 1 < (s ^ 2) ^ i := Nat.one_lt_pow hi0 (Nat.one_lt_pow (by norm_num) (by omega))
    omega
  have hne2 : ∀ i ∈ Icc 2 n, (if Even i then s ^ i - 1 else s ^ i + 1) ≠ 0 := by
    intro i hi
    have hi0 : i ≠ 0 := by have := (mem_Icc.mp hi).1; omega
    have h1 : 1 < s ^ i := Nat.one_lt_pow hi0 (by omega)
    split_ifs <;> omega
  rw [lieOrderNumerator, lieOrderNumerator,
    padicValNat.mul (pow_ne_zero _ hs20) (Finset.prod_ne_zero_iff.mpr hne1),
    padicValNat.mul (pow_ne_zero _ hs0) (Finset.prod_ne_zero_iff.mpr hne2),
    CFSG.Permutation.SylowTwoNormalizer.padicValNat_prod _ hne1,
    CFSG.Permutation.SylowTwoNormalizer.padicValNat_prod _ hne2]
  have hsnd : ¬ 3 ∣ s := by omega
  have hs2nd : ¬ 3 ∣ s ^ 2 := by
    have h := pow_mod_three_of_mod_two_even hs3 (show Even 2 by norm_num)
    omega
  have hL : padicValNat 3 ((s ^ 2) ^ (n * (n - 1) / 2)) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hs2nd, mul_zero]
  have hR : padicValNat 3 (s ^ (n * (n - 1) / 2)) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hsnd, mul_zero]
  rw [hL, hR]
  simp only [zero_add]
  exact Finset.sum_congr rfl fun i hi =>
    padicValNat_three_pow_two_mul_sub_one hs hs3 (mem_Icc.mp hi).1

end CFSG.LocalAnalysis.Gross82.OrderThree
