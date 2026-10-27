module

public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped MatrixGroups

theorem exists_nonsquare_of_two_ne_zero {K : Type*} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) :
    ∃ ν : K, ¬ IsSquare ν := by
  have hring : ringChar K ≠ 2 := by
    intro h
    apply h2
    have := (ringChar.spec K 2).2 (by rw [h])
    exact_mod_cast this
  exact FiniteField.exists_nonsquare hring

theorem card_range_eq_of_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) : Nat.card f.range = Nat.card G :=
  (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem card_specialLinear_two {F : Type*} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring,
    Nat.mul_div_cancel _ (by
      rcases Nat.lt_or_ge q 2 with h | h
      · have : 2 ≤ q := by
          have := Fintype.one_lt_card (α := F)
          rw [← Nat.card_eq_fintype_card] at this
          omega
        omega
      · omega)]

theorem card_orthogonalGroup_quadOdd_two {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 2 F)) =
      2 * Nat.card (StatedSp 2 F) := by
  have h := card_orthogonalGroup_quadOdd_of_two_ne_zero h2 2
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have e : Finset.Icc 1 2 = {1, 2} := by decide
  rw [e, Finset.prod_pair (by norm_num)] at h ⊢
  have h1 : 1 ≤ Nat.card F ^ (2 * 1) := Nat.one_le_pow _ _ hq
  have h2' : 1 ≤ Nat.card F ^ (2 * 2) := Nat.one_le_pow _ _ hq
  zify [h1, h2']
  linear_combination h

theorem card_orthogonalGroup_quadOdd_one {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd 1 F)) =
      2 * Nat.card SL(2, F) := by
  have h := card_orthogonalGroup_quadOdd_of_two_ne_zero h2 1
  rw [card_specialLinear_two]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have e : Finset.Icc 1 1 = {1} := by decide
  rw [e, Finset.prod_singleton] at h
  have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ hq
  zify [h1]
  linear_combination h

end CFSG.ClassicalInvolution.PhanB3.S
