module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig

open Subgroup

theorem subsingleton_sylow_five {Z : Type*} [Group Z] [Finite Z] (hZ : Nat.card Z ∣ 40)
    (h5 : 5 ∣ Nat.card Z) : Subsingleton (Sylow 5 Z) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : Nat.card Z = 5 ∨ Nat.card Z = 10 ∨ Nat.card Z = 20 ∨ Nat.card Z = 40 := by
    have hmem : Nat.card Z ∈ Nat.divisors 40 := Nat.mem_divisors.2 ⟨hZ, by norm_num⟩
    have hd : Nat.divisors 40 = {1, 2, 4, 5, 8, 10, 20, 40} := by decide
    rw [hd] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hfac : (Nat.card Z).factorization 5 = 1 := by
    rw [Nat.factorization_def _ Nat.prime_five]
    rcases hn with h | h | h | h <;> rw [h] <;> decide +kernel
  let P : Sylow 5 Z := default
  have hPcard : Nat.card P = 5 := by rw [Sylow.card_eq_multiplicity, hfac, pow_one]
  have hidx : (P : Subgroup Z).index ∣ 8 := by
    have h1 := (P : Subgroup Z).card_mul_index
    rw [hPcard] at h1
    have : 5 * (P : Subgroup Z).index ∣ 40 := by rw [h1]; exact hZ
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5)).1 (by simpa using this)
  have hcard := P.card_eq_index_normalizer
  have hdvd : Nat.card (Sylow 5 Z) ∣ 8 :=
    hcard ▸ (Subgroup.index_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup Z)))).trans hidx
  have hmod := card_sylow_modEq_one 5 Z
  have hone : Nat.card (Sylow 5 Z) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 5 Z) <;> omega
  exact (Nat.card_eq_one_iff_unique.1 hone).1

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig
