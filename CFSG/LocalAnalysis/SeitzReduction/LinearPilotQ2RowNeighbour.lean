module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowRev

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

section Order3

variable {n : ℕ} {K : Type*} [Field K]

theorem braid_single_of_charTwo [CharP K 2] {a b : Fin n} (hab : a ≠ b) :
    ((1 : Matrix (Fin n) (Fin n) K) + single a b 1) * (1 + single b a 1) * (1 + single a b 1) =
      (1 + single b a 1) * (1 + single a b 1) * (1 + single b a 1) := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hE2 : single a b (1 : K) + single a b 1 = 0 := by rw [← single_add, h2, single_zero]
  have hE2' : single b a (1 : K) + single b a 1 = 0 := by rw [← single_add, h2, single_zero]
  have e1 : single a b (1 : K) * single a b 1 = 0 := single_mul_single_of_ne _ _ _ _ (Ne.symm hab) _
  have e2 : single b a (1 : K) * single b a 1 = 0 := single_mul_single_of_ne _ _ _ _ hab _
  have e3 : single a b (1 : K) * single b a 1 = single a a 1 := by
    rw [single_mul_single_same, mul_one]
  have e4 : single b a (1 : K) * single a b 1 = single b b 1 := by
    rw [single_mul_single_same, mul_one]
  have e5 : single a a (1 : K) * single a b 1 = single a b 1 := by
    rw [single_mul_single_same, mul_one]
  have e6 : single b b (1 : K) * single b a 1 = single b a 1 := by
    rw [single_mul_single_same, mul_one]
  have key : ((1 : Matrix (Fin n) (Fin n) K) + single a b 1) * (1 + single b a 1) *
      (1 + single a b 1) = (1 + single b a 1) * (1 + single a b 1) * (1 + single b a 1) +
        ((single a b (1 : K) + single a b 1) - (single b a (1 : K) + single b a 1)) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, e1, e2, e3, e4,
      e5, e6]
    abel
  rw [key, hE2, hE2', sub_self, add_zero]

theorem specialLinear_transvection_mul_self_of_charTwo [CharP K 2] {i j : Fin n} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : K) * SpecialLinearGroup.transvection hij 1 = 1 := by
  apply Subtype.ext
  change ((1 : Matrix (Fin n) (Fin n) K) + single i j 1) * (1 + single i j 1) = 1
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have e1 : single i j (1 : K) * single i j 1 = 0 := single_mul_single_of_ne _ _ _ _ (Ne.symm hij) _
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, e1, add_zero]
  rw [add_assoc, ← single_add, h2, single_zero, add_zero]

theorem order3Elt_pow_three [CharP K 2] {a b : Fin n} (hab : a ≠ b) :
    order3Elt K hab ^ 3 = 1 := by
  set u := SpecialLinearGroup.transvection hab (1 : K) with hu
  set v := SpecialLinearGroup.transvection (Ne.symm hab) (1 : K) with hv
  have huu : u * u = 1 := specialLinear_transvection_mul_self_of_charTwo hab
  have hvv : v * v = 1 := specialLinear_transvection_mul_self_of_charTwo (Ne.symm hab)
  have hbraid : u * v * u = v * u * v := Subtype.ext (braid_single_of_charTwo hab)
  have h3 : (u * v) ^ 3 = 1 :=
    calc (u * v) ^ 3 = (u * v * u) * (v * u * v) := by rw [pow_three]; simp only [mul_assoc]
      _ = (v * u * v) * (v * u * v) := by rw [hbraid]
      _ = v * u * (v * v) * u * v := by group
      _ = 1 := by
        rw [hvv, mul_one, mul_assoc v u u, huu, mul_one, hvv]
  rw [order3Elt, ← map_pow, h3, map_one]

theorem order3Elt_mem_of_card_eq_three [CharP K 2] (hK : Nat.card K = 2) (hn : 3 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = 3) : order3Elt K hab ∈ X₀ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  set J := rootSL2 (K := K) a b with hJ
  have hJc : Nat.card J = 6 := by
    obtain ⟨φ⟩ := rootSL2_mulEquiv (K := K) hab hn
    rw [Nat.card_congr φ.toEquiv, Matrix.card_SL_field, ← Nat.card_eq_fintype_card, hK]
    decide
  set X' := X₀.subgroupOf J with hX'
  have hX'c : Nat.card X' = 3 := by
    rw [hX', Nat.card_congr (subgroupOfEquivOfLe hX₀).toEquiv, hX₀c]
  have hidx : X'.index = 2 := by
    have h := X'.card_mul_index
    rw [hX'c, hJc] at h
    omega
  have : X'.Normal := Subgroup.normal_of_index_eq_two hidx
  set y : J := ⟨order3Elt K hab, order3Elt_mem_rootSL2 hab⟩ with hy
  have hy3 : y ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact order3Elt_pow_three hab)
  have hQ : Nat.card (J ⧸ X') = 2 := by rw [← Subgroup.index, hidx]
  have h2 : (QuotientGroup.mk y : J ⧸ X') ^ 2 = 1 := by
    rw [← hQ]
    exact pow_card_eq_one'
  have h3 : (QuotientGroup.mk y : J ⧸ X') ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hy3, QuotientGroup.mk_one]
  have h1 : (QuotientGroup.mk y : J ⧸ X') = 1 := by
    calc (QuotientGroup.mk y : J ⧸ X') = (QuotientGroup.mk y : J ⧸ X') ^ 3 *
          ((QuotientGroup.mk y : J ⧸ X') ^ 2)⁻¹ := by group
      _ = 1 := by rw [h2, h3, inv_one, mul_one]
  have hyX : y ∈ X' := (QuotientGroup.eq_one_iff y).1 h1
  exact mem_subgroupOf.1 hyX

end Order3

end CFSG.SeitzReduction.LinearPilot
