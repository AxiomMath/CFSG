module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open CFSG

attribute [local instance] Classical.propDecidable

universe u

variable {A : Type u} [Group A]

theorem isKleinFour_of_elementary_card_four [Finite A] [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 4) : IsKleinFour A := by
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩

theorem mem_zpowers_of_square_one {c x : A} (hc : c * c = 1) :
    x ∈ Subgroup.zpowers c ↔ x = 1 ∨ x = c := by
  classical
  constructor
  · intro hx
    have hpow : c ^ 2 = 1 := by simpa only [pow_two] using hc
    have hfinite : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by omega, hpow⟩
    obtain ⟨n, rfl⟩ := hfinite.mem_powers_iff_mem_zpowers.mpr hx
    have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
    have hmod : c ^ n = c ^ (n % 2) := pow_eq_pow_mod n hpow
    rcases hn with hn | hn
    · left
      simpa [hn] using hmod
    · right
      simpa [hn] using hmod
  · rintro (hx | hx)
    · simpa only [hx] using (Subgroup.zpowers c).one_mem
    · simpa only [hx] using Subgroup.mem_zpowers c

def fourGroupCoefficientSubgroup (a b : A) : Fin 5 → Subgroup A :=
  ![⊤, ⊥, Subgroup.zpowers a, Subgroup.zpowers b, Subgroup.zpowers (a * b)]

def fourGroupCoefficientLeft : Fin 5 → ℕ := ![1, 2, 0, 0, 0]

def fourGroupCoefficientRight : Fin 5 → ℕ := ![0, 0, 1, 1, 1]

theorem fourGroupCoefficient_relation [Finite A] [IsKleinFour A]
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (x : A) :
    (∑ i : Fin 5, if x ∈ fourGroupCoefficientSubgroup a b i then
      fourGroupCoefficientLeft i else 0) =
    ∑ i : Fin 5, if x ∈ fourGroupCoefficientSubgroup a b i then
      fourGroupCoefficientRight i else 0 := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hcases : x = a * b ∨ x = a ∨ x = b ∨ x = 1 := by
    have hx : x ∈ ({a * b, a, b, (1 : A)} : Finset A) := by
      rw [IsKleinFour.eq_finset_univ ha hb hab]
      exact Finset.mem_univ x
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
  have hab1 : a * b ≠ 1 := by
    intro h
    exact hab (mul_eq_one_iff_eq_inv.mp h |>.trans (IsKleinFour.inv_eq_self b))
  have haba : a * b ≠ a := by
    intro h
    exact hb (mul_left_cancel (show a * b = a * 1 by simpa using h))
  have habb : a * b ≠ b := by
    intro h
    exact ha (mul_right_cancel (show a * b = 1 * b by simpa using h))
  simp only [fourGroupCoefficientSubgroup, fourGroupCoefficientLeft,
      fourGroupCoefficientRight, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Subgroup.mem_top, Subgroup.mem_bot, ite_true,
      mem_zpowers_of_square_one (IsKleinFour.mul_self a),
      mem_zpowers_of_square_one (IsKleinFour.mul_self b),
      mem_zpowers_of_square_one (IsKleinFour.mul_self (a * b))]
  rcases hcases with hx | hx | hx | hx <;> subst x <;> simp_all [eq_comm]

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
