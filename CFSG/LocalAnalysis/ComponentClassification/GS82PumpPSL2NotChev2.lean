module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem mul_sq_sub_one_add_self (x : ℕ) : x * (x ^ 2 - 1) + x = x ^ 3 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
    calc x * (x ^ 2 - 1) + x = x * (x ^ 2 - 1 + 1) := by ring
      _ = x ^ 3 := by rw [Nat.sub_add_cancel h1]; ring

theorem sq_mul_le_cube {a q : ℕ} (h : a ≤ q) : a ^ 2 * q ≤ q ^ 3 :=
  calc a ^ 2 * q ≤ q ^ 2 * q := Nat.mul_le_mul_right q (Nat.pow_le_pow_left h 2)
    _ = q ^ 3 := by ring

theorem two_mul_card_add_eq_cube (hO : LieOrderFormulasInput) {Y : Type} [Group Y] {r e : ℕ}
    (hr2 : r ≠ 2) (hY : Blueprint.LieModel Y .PSL 2 r e) :
    2 * Nat.card Y + r ^ e = (r ^ e) ^ 3 := by
  have hadm := Blueprint.LieModel.admissible hY
  obtain ⟨-, hord, -⟩ := hO Y .PSL 2 r e hadm hY
  have hodd : Odd (r ^ e) := (hadm.1.odd_of_ne_two hr2).pow
  generalize r ^ e = q at hord hodd ⊢
  simp only [lieOrderNumerator, lieOrderDivisor, Finset.Icc_self, Finset.prod_singleton,
    Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, pow_one] at hord
  have hg : Nat.gcd 2 (q - 1) = 2 := Nat.gcd_eq_left (by obtain ⟨k, rfl⟩ := hodd; simp)
  rw [hg] at hord
  have := mul_sq_sub_one_add_self q
  omega

open HardMathSupport.Dickson.Sec6.I923 HardMathSupport.Solomon.Proving in
theorem not_inChev2_of_lieModel_psl_two_of_orders (hO : LieOrderFormulasInput) {Y : Type}
    [Group Y] {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hq : r ^ e ∉ ({3, 5, 7, 9} : Finset ℕ)) (hY : Blueprint.LieModel Y .PSL 2 r e) :
    ¬ GH74.GLS.InChev2 Y := by
  have hM := two_mul_card_add_eq_cube hO hr2 hY
  have hodd : Odd (r ^ e) := (hr.odd_of_ne_two hr2).pow
  have hq11 : 11 ≤ r ^ e := by
    have h3 : 3 ≤ r := by have := hr.two_le; omega
    have hle : r ≤ r ^ e := Nat.le_self_pow (by omega) r
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    obtain ⟨k, hk⟩ := hodd
    omega
  generalize r ^ e = q at hM hodd hq11
  rintro (⟨t, n, f, hadm, hX⟩ | ⟨⟨e6⟩⟩ | hU)
  · obtain ⟨-, hord, -⟩ := hO Y t n 2 f hadm hX
    by_cases ht : t = .Tits
    · subst ht
      simp only [lieOrderNumerator, lieOrderDivisor, mul_one] at hord
      rw [hord] at hM
      rcases le_or_gt q 330 with h | h
      · have := Nat.pow_le_pow_left h 3
        norm_num at this
        omega
      · have := sq_mul_le_cube (show 331 ≤ q by omega)
        norm_num at this
        omega
    by_cases hA : t = .PSL ∧ n = 2
    · obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by have := hadm.2.1; omega⟩
      set Q := 2 ^ (k + 1) with hQ
      simp only [lieOrderNumerator, lieOrderDivisor, Finset.Icc_self, Finset.prod_singleton,
        Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, pow_one] at hord
      have hQ2 : Q = 2 * 2 ^ k := by rw [hQ, pow_succ]; ring
      have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have hg : Nat.gcd 2 (Q - 1) = 1 :=
        Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega)))
      rw [hg, mul_one] at hord
      have hkey := mul_sq_sub_one_add_self Q
      have hmix : q ^ 3 + 2 * Q = 2 * Q ^ 3 + q := by omega
      have h5 := (mixed_core q k (by omega) hodd hmix).1
      omega
    · exact lie_order_ne_l2 hadm ht hA hord (by omega : 10 ≤ q) (fun _ => hM)
        (fun h => absurd hodd (Nat.not_odd_iff_even.2 h))
  · have hc : Nat.card Y = 360 := by
      rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    rw [hc] at hM
    have := sq_mul_le_cube hq11
    norm_num at this
    omega
  · have hadm := Blueprint.LieModel.admissible hU
    obtain ⟨-, hord, -⟩ := hO Y .PSU 3 3 1 hadm hU
    have h1 : lieOrderDivisor .PSU 3 (3 ^ 1) = 1 := by decide
    have h2 : lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 := by decide
    rw [h1, h2, mul_one] at hord
    rw [hord] at hM
    rcases le_or_gt q 22 with h | h
    · have := Nat.pow_le_pow_left h 3
      norm_num at this
      omega
    · have := sq_mul_le_cube (show 23 ≤ q by omega)
      norm_num at this
      omega

end CFSG.ComponentClassification.GS82PumpInputs
