module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.QTGen4.DSGen4

open scoped commutatorElement

section Quad

variable {W : Type*} [Group W]

open scoped Classical in
@[expose] noncomputable def bit (a : W) : ZMod 2 := if a = 1 then 0 else 1

theorem bit_eq_zero_iff {a : W} : bit a = 0 ↔ a = 1 := by
  classical
  unfold bit
  split_ifs with h <;> simp [h]

theorem bit_one : bit (1 : W) = 0 := bit_eq_zero_iff.mpr rfl

theorem bit_inv (a : W) : bit a⁻¹ = bit a := by
  classical
  unfold bit
  simp [inv_eq_one]

theorem eq_of_ne_one_of_card_two {Zw : Subgroup W} (hZ2 : Nat.card Zw = 2) {a b : W} (ha : a ∈ Zw)
    (hb : b ∈ Zw) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : Zw)).mp hZ2
  have ha' : (⟨a, ha⟩ : Zw) = y := huniq _ (fun h => ha1 (congrArg Subtype.val h))
  have hb' : (⟨b, hb⟩ : Zw) = y := huniq _ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (ha'.trans hb'.symm)

theorem mul_self_eq_one_of_card_two {Zw : Subgroup W} (hZ2 : Nat.card Zw = 2) {a : W}
    (ha : a ∈ Zw) : a * a = 1 := by
  by_cases ha1 : a = 1
  · subst ha1; simp
  by_contra hne
  have h2 := eq_of_ne_one_of_card_two hZ2 (Zw.mul_mem ha ha) ha hne ha1
  exact ha1 (mul_eq_left.mp h2)

theorem comm_of_card_two {Zw : Subgroup W} (hZ2 : Nat.card Zw = 2) {z : W} (hz : z ∈ Zw) (w : W)
    (hw : w * z * w⁻¹ ∈ Zw) : w * z = z * w := by
  by_cases hz1 : z = 1
  · subst hz1; simp
  have hne : w * z * w⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = w⁻¹ * (w * z * w⁻¹) * w := by group
    rw [this, h]; group
  have := eq_of_ne_one_of_card_two hZ2 hw hz hne hz1
  calc w * z = (w * z * w⁻¹) * w := by group
    _ = z * w := by rw [this]

theorem bit_mul {Zw : Subgroup W} (hZ2 : Nat.card Zw = 2) {a b : W} (ha : a ∈ Zw) (hb : b ∈ Zw) :
    bit (a * b) = bit a + bit b := by
  classical
  by_cases ha1 : a = 1
  · subst ha1; simp [bit_one]
  by_cases hb1 : b = 1
  · subst hb1; simp [bit_one]
  have hab : a = b := eq_of_ne_one_of_card_two hZ2 ha hb ha1 hb1
  subst hab
  rw [mul_self_eq_one_of_card_two hZ2 ha, bit_one]
  have h1 : bit a = 1 := by
    unfold bit; simp [ha1]
  rw [h1]
  decide

@[expose] noncomputable def sqb (x : W) : ZMod 2 := bit (x ^ 2)

@[expose] noncomputable def cb (x y : W) : ZMod 2 := bit ⁅x, y⁆

variable {Zw : Subgroup W}

theorem sq_mul_aux (x y c : W) (hc : c * x = x * c) (h1 : y * x = c⁻¹ * (x * y)) :
    (x * y) ^ 2 = c⁻¹ * x ^ 2 * y ^ 2 := by
  have hc' : x * c⁻¹ = c⁻¹ * x := by
    calc x * c⁻¹ = c⁻¹ * (c * x) * c⁻¹ := by group
      _ = c⁻¹ * (x * c) * c⁻¹ := by rw [hc]
      _ = c⁻¹ * x := by group
  calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
    _ = x * (c⁻¹ * (x * y)) * y := by rw [h1]
    _ = (x * c⁻¹) * x * y * y := by group
    _ = c⁻¹ * x * x * y * y := by rw [hc']
    _ = c⁻¹ * x ^ 2 * y ^ 2 := by simp only [pow_two, mul_assoc]

theorem sq_mul_eq {x y : W} (hc : ⁅x, y⁆ * x = x * ⁅x, y⁆) :
    (x * y) ^ 2 = ⁅x, y⁆⁻¹ * x ^ 2 * y ^ 2 := by
  refine sq_mul_aux x y _ hc ?_
  rw [commutatorElement_def]; group

theorem sqb_mul (hZ2 : Nat.card Zw = 2) (hcomm : ∀ x y : W, ⁅x, y⁆ ∈ Zw)
    (hsq : ∀ x : W, x ^ 2 ∈ Zw) (hcent : ∀ z ∈ Zw, ∀ w : W, z * w = w * z) (x y : W) :
    sqb (x * y) = sqb x + sqb y + cb x y := by
  unfold sqb cb
  rw [sq_mul_eq (hcent _ (hcomm x y) x), bit_mul hZ2 (Zw.mul_mem (Zw.inv_mem (hcomm x y)) (hsq x))
    (hsq y), bit_mul hZ2 (Zw.inv_mem (hcomm x y)) (hsq x), bit_inv]
  ring

theorem comm_mul_left (x1 x2 w : W) : ⁅x1 * x2, w⁆ = x1 * ⁅x2, w⁆ * x1⁻¹ * ⁅x1, w⁆ := by
  simp only [commutatorElement_def]; group

theorem cb_mul_left (hZ2 : Nat.card Zw = 2) (hcomm : ∀ x y : W, ⁅x, y⁆ ∈ Zw)
    (hcent : ∀ z ∈ Zw, ∀ w : W, z * w = w * z) (x1 x2 w : W) :
    cb (x1 * x2) w = cb x1 w + cb x2 w := by
  unfold cb
  rw [comm_mul_left]
  have h : x1 * ⁅x2, w⁆ * x1⁻¹ = ⁅x2, w⁆ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hcent _ (hcomm x2 w) x1).symm
  rw [h, bit_mul hZ2 (hcomm x2 w) (hcomm x1 w)]
  ring

theorem sqb_third_diff (hZ2 : Nat.card Zw = 2) (hcomm : ∀ x y : W, ⁅x, y⁆ ∈ Zw)
    (hsq : ∀ x : W, x ^ 2 ∈ Zw) (hcent : ∀ z ∈ Zw, ∀ w : W, z * w = w * z) (a b c : W) :
    sqb (a * b * c) + sqb (a * b) + sqb (a * c) + sqb (b * c) + sqb a + sqb b + sqb c = 0 := by
  rw [sqb_mul hZ2 hcomm hsq hcent (a * b) c, sqb_mul hZ2 hcomm hsq hcent a b,
    sqb_mul hZ2 hcomm hsq hcent a c, sqb_mul hZ2 hcomm hsq hcent b c,
    cb_mul_left hZ2 hcomm hcent a b c]
  generalize sqb a = s1
  generalize sqb b = s2
  generalize sqb c = s3
  generalize cb a b = c1
  generalize cb a c = c2
  generalize cb b c = c3
  revert s1 s2 s3 c1 c2 c3
  decide

end Quad

end CFSG.GH74.QTGen4.DSGen4
