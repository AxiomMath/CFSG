module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

public section

namespace CFSG.GroupTheory

variable {X Y : Type*} [Group X] [Group Y]

theorem le_normalizer_of_map_le_normalizer_of_ker_le (f : X →* Y) {A V : Subgroup X}
    (hker : f.ker ≤ V) (h : A.map f ≤ Subgroup.normalizer (V.map f)) :
    A ≤ Subgroup.normalizer V := by
  have key : ∀ b ∈ A, ∀ x ∈ V, b * x * b⁻¹ ∈ V := by
    intro b hb x hx
    have hfb : f b ∈ Subgroup.normalizer (V.map f) := h (Subgroup.mem_map_of_mem f hb)
    rw [Subgroup.mem_normalizer_iff] at hfb
    have hfx : f (b * x * b⁻¹) ∈ V.map f := by
      rw [map_mul, map_mul, map_inv]
      exact (hfb (f x)).mp (Subgroup.mem_map_of_mem f hx)
    obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hfx
    have hmem : (b * x * b⁻¹) * y⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfy, mul_inv_cancel]
    have hV := hker hmem
    have heq : b * x * b⁻¹ = ((b * x * b⁻¹) * y⁻¹) * y := by group
    rw [heq]
    exact V.mul_mem hV hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  have h1 := key a⁻¹ (A.inv_mem ha) (a * x * a⁻¹) hx
  have heq : a⁻¹ * (a * x * a⁻¹) * a = x := by group
  simpa [heq] using h1

end CFSG.GroupTheory
