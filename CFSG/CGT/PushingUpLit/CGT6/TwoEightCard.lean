module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

theorem two_pow_le_of_dvd {q e k : ℕ} (hq : 2 ≤ q) (hqe : Even q)
    (h : 2 ^ k ∣ (q * (q ^ 2 - 1)) ^ e) : 2 ^ k ≤ q ^ e := by
  have hodd : Odd (q ^ 2 - 1) := by
    have h1 : Even (q ^ 2) := hqe.pow_of_ne_zero (by norm_num)
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    obtain ⟨r, hr⟩ := h1
    exact ⟨r - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ k) ((q ^ 2 - 1) ^ e) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (hodd.pow))
  rw [mul_pow] at h
  exact Nat.le_of_dvd (pow_pos (by omega) e) (hcop.dvd_of_dvd_mul_right h)

theorem card_le_of_isPGroup_two {G : Type*} [Group G] [Finite G] {q e : ℕ} (hq : 2 ≤ q)
    (hqe : Even q) (hG : Nat.card G = (q * (q ^ 2 - 1)) ^ e) (T : Subgroup G) (hT : IsPGroup 2 T) :
    Nat.card T ≤ q ^ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hT
  have hdvd : Nat.card T ∣ Nat.card G := Subgroup.card_subgroup_dvd_card T
  rw [hk, hG] at hdvd
  rw [hk]
  exact two_pow_le_of_dvd hq hqe hdvd

theorem card_two_of_charTwo {K : Type*} [Field K] [Finite K] [CharP K 2] :
    2 ≤ Nat.card K ∧ Even (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hm]
  refine ⟨?_, ?_⟩
  · calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m : ℕ) := Nat.pow_le_pow_right (by norm_num) m.pos
  · exact (Nat.even_pow.mpr ⟨even_two, m.pos.ne'⟩)

theorem card_le_of_isPGroup_sl2 {K : Type*} [Field K] [Finite K] [CharP K 2]
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (hT : IsPGroup 2 T) :
    Nat.card T ≤ Nat.card K := by
  obtain ⟨h2, he⟩ := card_two_of_charTwo (K := K)
  have := card_le_of_isPGroup_two (G := Matrix.SpecialLinearGroup (Fin 2) K) (q := Nat.card K)
    (e := 1) h2 he (by rw [pow_one]; exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K)
    T hT
  simpa using this

theorem card_le_of_isPGroup_sl2_prod {K : Type*} [Field K] [Finite K] [CharP K 2]
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K))
    (hT : IsPGroup 2 T) : Nat.card T ≤ Nat.card K ^ 2 := by
  obtain ⟨h2, he⟩ := card_two_of_charTwo (K := K)
  refine card_le_of_isPGroup_two (q := Nat.card K) (e := 2) h2 he ?_ T hT
  rw [Nat.card_prod, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K, ← sq]

end CFSG.CGT.PushingUpLit.CGT6.TwoEight
