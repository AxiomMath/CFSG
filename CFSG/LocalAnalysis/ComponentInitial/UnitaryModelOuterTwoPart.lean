module

public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Finset Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank

theorem unitary_model_outer_two_part_bound (T : Type) [Group T] (n p f : ℕ)
    (h : StatedClassicalModel T .PSU n p f) :
    (Nat.card T : ℤ) * (Nat.gcd n (p ^ f + 1) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ j ∈ Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ j - (-1) ^ j) ∧
    (Nat.card T : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        (∏ j ∈ Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ j - (-1) ^ j)) / (Nat.gcd n (p ^ f + 1) : ℤ) ∧
      Nat.card (Outer T) = 2 * f * Nat.gcd n (p ^ f + 1) ∧
      4 ≤ ordProj[2] (Nat.card T) ∧
      ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) := by
  obtain ⟨⟨hp, hf, hn, h32⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq32 : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨h3, h2⟩ => h32 (by rw [h3, h2])
  set q := p ^ f with hq
  set N := n * (n - 1) / 2 with hN
  set d := Nat.gcd n (q + 1) with hd
  let e' : T ≃* unitaryPSU hU n := e.trans (unitaryPSUEquiv hU (by omega)).symm
  have hcardT : Nat.card T = Nat.card (unitaryPSU hU n) := Nat.card_congr e'.toEquiv
  have hout : Nat.card (Outer T) = 2 * f * d := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact (UnitaryHigher.unitary_full_diagonal_outer_order hU (by omega) hq32).2.2.2.2.1
  have hSint : (Nat.card (unitarySU p f K n) : ℤ) = ((q : ℕ) : ℤ) ^ N *
      ∏ j ∈ Icc 2 n, (((q : ℕ) : ℤ) ^ j - (-1) ^ j) := by
    have hB := gramForm_isSymm hU (G := (1 : Matrix (Fin n) (Fin n) K)) (by
      rw [Matrix.map_one _ (map_zero hU.bar) (map_one hU.bar), transpose_one])
    have hBl := gramForm_separatingLeft hU (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp)
    have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
    rw [unitarySU_eq_gramSU hU, card_gramSU]
    exact (unitary_full_group_order hU hB hBl hdim (by omega)).2.1
  have hZ : Nat.card (unitaryScalars hU n) = d := card_unitaryScalars hU (by omega)
  have hSZ : Nat.card (unitarySU p f K n) = Nat.card (unitaryPSU hU n) * d := by
    rw [← hZ]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hp2le := hp.two_le
  have hq2 : 2 ≤ q := le_trans hp2le (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
  have hfacpos : ∀ j ∈ Icc 2 n, 0 < ((q : ℕ) : ℤ) ^ j - (-1) ^ j := by
    intro j hj
    have hqj : (2 : ℤ) ≤ ((q : ℕ) : ℤ) ^ j := by
      calc (2 : ℤ) ≤ ((q : ℕ) : ℤ) := by exact_mod_cast hq2
        _ = ((q : ℕ) : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ ((q : ℕ) : ℤ) ^ j := pow_le_pow_right₀ (by omega) (by simp at hj; omega)
    rcases neg_one_pow_eq_or ℤ j with h1 | h1 <;> rw [h1] <;> omega
  have hd0 : d ≠ 0 := Nat.gcd_ne_zero_left (by omega)
  have hexact : (Nat.card T : ℤ) * (d : ℤ) = ((q : ℕ) : ℤ) ^ N *
      ∏ j ∈ Icc 2 n, (((q : ℕ) : ℤ) ^ j - (-1) ^ j) := by
    rw [← hSint, hSZ, hcardT, Nat.cast_mul]
  have hord : (Nat.card T : ℤ) = ((q : ℕ) : ℤ) ^ N *
      (∏ j ∈ Icc 2 n, (((q : ℕ) : ℤ) ^ j - (-1) ^ j)) / (d : ℤ) := by
    rw [← hexact, Int.mul_ediv_cancel _ (by exact_mod_cast hd0)]
  refine ⟨hexact, hord, hout, ?_⟩
  set P := ∏ j ∈ Icc 2 n, (((q : ℕ) : ℤ) ^ j - (-1) ^ j).natAbs with hP
  have hSnat : Nat.card (unitarySU p f K n) = q ^ N * P := by
    have h1 := congrArg Int.natAbs hSint
    rw [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h1
    rw [h1, hP]
    congr 1
    exact map_prod Int.natAbsHom _ _
  have hfac0 : ∀ j ∈ Icc 2 n, (((q : ℕ) : ℤ) ^ j - (-1) ^ j).natAbs ≠ 0 := fun j hj =>
    Int.natAbs_ne_zero.mpr (hfacpos j hj).ne'
  have hP0 : P ≠ 0 := prod_ne_zero_iff.mpr hfac0
  have hqN0 : q ^ N ≠ 0 := pow_ne_zero _ (by omega)
  have hmul : Nat.card T * d = q ^ N * P := by rw [hcardT, ← hSZ, hSnat]
  have hT0 : Nat.card T ≠ 0 := fun h0 => mul_ne_zero hqN0 hP0 (by rw [← hmul, h0, zero_mul])
  have h2adic : ordProj[2] (Nat.card T) * ordProj[2] d = ordProj[2] (q ^ N) * ordProj[2] P := by
    rw [← Nat.ordProj_mul 2 hT0 hd0, hmul, Nat.ordProj_mul 2 hqN0 hP0]
  have hPprod : ordProj[2] P =
      ∏ j ∈ Icc 2 n, ordProj[2] ((((q : ℕ) : ℤ) ^ j - (-1) ^ j).natAbs) :=
    ordProj_two_prod _ _ hfac0
  have hfbounds := (lie_order_two_adic_arithmetic).2.2 f hf
  have hf2pos : 0 < ordProj[2] f := Nat.ordProj_pos f 2
  have hd2pos : 0 < ordProj[2] d := Nat.ordProj_pos d 2
  have h2 : ordProj[2] 2 = 2 := ordProj_two_two_pow 1
  have ho : ordProj[2] (Nat.card (Outer T)) = 2 * ordProj[2] f * ordProj[2] d := by
    rw [hout, Nat.ordProj_mul 2 (mul_ne_zero (by norm_num) (by omega)) hd0,
      Nat.ordProj_mul 2 (by norm_num) (by omega), h2]
  have hN3 : 3 ≤ N := by
    rw [hN]
    have : 6 ≤ n * (n - 1) := le_trans (by norm_num : 6 ≤ 3 * 2) (Nat.mul_le_mul hn (by omega))
    omega
  rcases eq_or_ne p 2 with rfl | hp2
  ·
    have hqeven : Even q := (Nat.even_pow' (by omega)).mpr even_two
    have hP1 : ordProj[2] P = 1 := by
      rw [hPprod]
      refine prod_eq_one fun j hj => ordProj_two_eq_one_of_odd ?_
      have hj1 : j ≠ 0 := by simp at hj; omega
      have hqje : Even (q ^ j) := (Nat.even_pow' hj1).mpr hqeven
      rcases neg_one_pow_eq_or ℤ j with h1 | h1
      · have hcast : (((q : ℕ) : ℤ) ^ j - (-1) ^ j).natAbs = q ^ j - 1 := by
          have hle : 1 ≤ q ^ j := Nat.one_le_pow _ _ (by omega)
          rw [h1, ← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_sub hle, Int.natAbs_natCast]
        rw [hcast]
        exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) hqje odd_one
      · have hcast : (((q : ℕ) : ℤ) ^ j - (-1) ^ j).natAbs = q ^ j + 1 := by
          rw [h1, sub_neg_eq_add, ← Nat.cast_pow, ← Nat.cast_one, ← Nat.cast_add,
            Int.natAbs_natCast]
        rw [hcast]
        exact hqje.add_odd odd_one
    have hd1 : ordProj[2] d = 1 :=
      ordProj_two_eq_one_of_odd (Odd.of_dvd_nat (hqeven.add_odd odd_one)
        (Nat.gcd_dvd_right n (q + 1)))
    have ha : ordProj[2] (Nat.card T) = 2 ^ (f * N) := by
      rw [hd1, mul_one, hP1, mul_one, hq, ← pow_mul, ordProj_two_two_pow] at h2adic
      exact h2adic
    have hle : 2 ^ (3 * f) ≤ 2 ^ (f * N) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm 3 f]; exact Nat.mul_le_mul_left f hN3)
    have h8 : 8 ≤ 2 ^ (3 * f) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [ha, ho, hd1, mul_one]
    exact ⟨by omega, by omega⟩
  ·
    have hqodd : Odd q := (hp.odd_of_ne_two hp2).pow
    have hqN1 : ordProj[2] (q ^ N) = 1 := ordProj_two_eq_one_of_odd hqodd.pow
    rw [hqN1, one_mul] at h2adic
    have h8 := ((lie_order_two_adic_arithmetic).1 p f hp hp2 hf).2
    rw [← hq] at h8
    have hprod := (lie_order_two_adic_arithmetic).2.1 p f n hp hp2 hf hn (-1) (Or.inr rfl)
    rw [← hq] at hprod
    have hgcd : Int.gcd (n : ℤ) ((q : ℤ) - -1) = d := by
      rw [hd, ← Int.gcd_natCast_natCast, Nat.cast_add, Nat.cast_one, sub_neg_eq_add]
    rw [hgcd, ← hPprod] at hprod
    have key : 8 * ordProj[2] d * ordProj[2] f ≤ ordProj[2] (Nat.card T) := by
      have hmul' : ordProj[2] d * (8 * ordProj[2] d * ordProj[2] f) ≤
          ordProj[2] d * ordProj[2] (Nat.card T) := by
        rw [mul_comm (ordProj[2] d) (ordProj[2] (Nat.card T)), h2adic]
        calc ordProj[2] d * (8 * ordProj[2] d * ordProj[2] f) =
            ordProj[2] d ^ 2 * (8 * ordProj[2] f) := by ring
          _ ≤ ordProj[2] d ^ 2 * ordProj[2] (q ^ 2 - 1) := Nat.mul_le_mul_left _ h8
          _ ≤ ordProj[2] P := hprod
      exact Nat.le_of_mul_le_mul_left hmul' hd2pos
    have hkey : 8 * (ordProj[2] f * ordProj[2] d) ≤ ordProj[2] (Nat.card T) := by
      rw [mul_comm (ordProj[2] f), ← mul_assoc]
      exact key
    have hfd : 0 < ordProj[2] f * ordProj[2] d := Nat.mul_pos hf2pos hd2pos
    have hlin : ∀ x y : ℕ, 0 < x → 8 * x ≤ y → 4 ≤ y ∧ 2 * x < y := fun x y hx hxy =>
      ⟨by omega, by omega⟩
    rw [ho, mul_assoc]
    exact hlin _ _ hfd hkey

end CFSG.LocalAnalysis.ComponentInitial
