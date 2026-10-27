module

public import Mathlib.Combinatorics.SimpleGraph.Init
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.GroupActions

variable {G : Type*} [Group G]

theorem braid_of_involutions {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h3 : (a * b) ^ 3 = 1) : a * b * a = b * a * b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : (a * b * a) * (b * a * b) = 1 := by
    rw [← h3]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h := eq_inv_of_mul_eq_one_left h1
  rw [h, mul_inv_rev, mul_inv_rev, ha', hb', mul_assoc]

end CFSG.GroupActions
