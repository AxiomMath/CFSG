module

public import CFSG.GH74.L5U5.ModelsBasic
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

theorem rcard_factorization_two_succ_le {N m : ℕ} (hN : N ≠ 0) (hm0 : m ≠ 0) (hm : 2 ∣ m) :
    N.factorization 2 + 1 ≤ (N * m).factorization 2 := by
  rw [Nat.factorization_mul hN hm0, Finsupp.add_apply]
  have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hm0 hm
  omega

theorem card2_lin {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (Nat.card SL(4, F)).factorization 2 + 1 ≤ (Nat.card SL(5, F)).factorization 2 := by
  have h4 := CFSG.OrderReductions.LinearOrders.card_specialLinear F 4 (by norm_num)
  have h5 := CFSG.OrderReductions.LinearOrders.card_specialLinear F 5 (by norm_num)
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  set q := Nat.card F with hqdef
  have hq5 : 1 < q ^ 5 := Nat.one_lt_pow (by norm_num) (by omega)
  have hprod : ∏ i ∈ Finset.Icc 2 5, (q ^ i - 1) =
      (∏ i ∈ Finset.Icc 2 4, (q ^ i - 1)) * (q ^ 5 - 1) :=
    Finset.prod_Icc_succ_top (by norm_num) _
  have key : Nat.card SL(5, F) = Nat.card SL(4, F) * (q ^ 4 * (q ^ 5 - 1)) := by
    rw [h5, h4, hprod]
    norm_num
    ring
  have hN : Nat.card SL(4, F) ≠ 0 := Nat.card_pos.ne'
  have hm0 : q ^ 4 * (q ^ 5 - 1) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega)
  have hm : 2 ∣ q ^ 4 * (q ^ 5 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have := Nat.odd_iff.1 (hodd.pow (n := 5))
    omega
  rw [key]
  exact rcard_factorization_two_succ_le hN hm0 hm

theorem odd_card_center_lin5 {F : Type} [Field F] [Finite F] :
    Odd (Nat.card (Subgroup.center SL(5, F))) := by
  rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 5 (by norm_num)]
  exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 5 _)

theorem rcard_exists_unitaryFieldData {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) : ∃ p f : ℕ, UnitaryFieldData p f F ∧ q = p ^ f := by
  obtain ⟨p, f, hp, -, rfl⟩ := CFSG.GH74.L5U5.exists_prime_pow_of_card_eq_sq hF
  have hf : 1 ≤ f := by
    by_contra hf0
    have hf0' : f = 0 := by omega
    subst hf0'
    have : 1 < Nat.card F := Finite.one_lt_card
    simp at hF
    omega
  exact ⟨p, f, ⟨hp.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩, rfl⟩

theorem rcard_card_statedSU {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card ↥(StatedSU n (p ^ f) K) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun K) hn).2.1
  rw [show StatedSU n (p ^ f) K = unitarySU p f K n from rfl, unitarySU_eq_gramSU h, card_gramSU]
  exact hU

theorem rcard_uni_ratio (Q : ℕ) :
    ((Q : ℤ) ^ (5 * (5 - 1) / 2) * ∏ i ∈ Finset.Icc 2 5, ((Q : ℤ) ^ i - (-1) ^ i)) =
      ((Q : ℤ) ^ (4 * (4 - 1) / 2) * ∏ i ∈ Finset.Icc 2 4, ((Q : ℤ) ^ i - (-1) ^ i)) *
        ((Q ^ 4 * (Q ^ 5 + 1) : ℕ) : ℤ) := by
  rw [Finset.prod_Icc_succ_top (by norm_num)]
  push_cast
  norm_num
  ring

theorem card2_uni {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : Odd q) :
    (Nat.card ↥(StatedSU 4 q F)).factorization 2 + 1 ≤
      (Nat.card ↥(StatedSU 5 q F)).factorization 2 := by
  obtain ⟨p, f, h, rfl⟩ := rcard_exists_unitaryFieldData hF
  have hq1 : 1 < p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    exact (Nat.one_lt_pow_iff two_ne_zero).1 h1
  have key : Nat.card ↥(StatedSU 5 (p ^ f) F) =
      Nat.card ↥(StatedSU 4 (p ^ f) F) * ((p ^ f) ^ 4 * ((p ^ f) ^ 5 + 1)) := by
    have := rcard_uni_ratio (p ^ f)
    rw [← rcard_card_statedSU h (n := 5) (by norm_num),
      ← rcard_card_statedSU h (n := 4) (by norm_num)] at this
    exact_mod_cast this
  have hN : Nat.card ↥(StatedSU 4 (p ^ f) F) ≠ 0 := Nat.card_pos.ne'
  have hm0 : (p ^ f) ^ 4 * ((p ^ f) ^ 5 + 1) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega)
  have hm : 2 ∣ (p ^ f) ^ 4 * ((p ^ f) ^ 5 + 1) := by
    refine Dvd.dvd.mul_left ?_ _
    have := Nat.odd_iff.1 (hq.pow (n := 5))
    omega
  rw [key]
  exact rcard_factorization_two_succ_le hN hm0 hm

theorem odd_card_center_uni5 {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) :
    Odd (Nat.card (Subgroup.center ↥(StatedSU 5 q F))) := by
  obtain ⟨p, f, h, rfl⟩ := rcard_exists_unitaryFieldData hF
  have : Fact p.Prime := ⟨h.prime⟩
  have hc := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := F) (p := p)
    (f := f) (n := 5) hF (by norm_num) (by simp)).2
  rw [hc, (CFSG.LinearGroups.unitary_scalar_kernel h.prime hF (n := 5) (by norm_num)).2.2]
  exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 5 _)

end CFSG.GH74.Generic.S1
