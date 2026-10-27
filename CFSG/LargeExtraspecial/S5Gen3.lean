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

namespace CFSG.LargeExtraspecial.S5

open Subgroup

variable {X : Type*} [Group X]

theorem mul_injective_of_inf_eq_bot {A B : Subgroup X} (h : A ⊓ B = ⊥) :
    Function.Injective fun p : A × B => (p.1 : X) * p.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  simp only at hab
  have hm : (a' : X)⁻¹ * a = b' * (b : X)⁻¹ := by
    calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * (a * b) * (b : X)⁻¹ := by group
      _ = (a' : X)⁻¹ * (a' * b') * (b : X)⁻¹ := by rw [hab]
      _ = b' * (b : X)⁻¹ := by group
  have h1 : (a' : X)⁻¹ * a ∈ A ⊓ B :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem a'.2) a.2, hm ▸ mul_mem b'.2 (inv_mem b.2)⟩
  rw [h, mem_bot] at h1
  have ha : (a : X) = a' := by
    calc (a : X) = a' * ((a' : X)⁻¹ * a) := by group
      _ = a' := by rw [h1, mul_one]
  have hb : (b : X) = b' := by
    rw [ha] at hab
    exact mul_left_cancel hab
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)

theorem card_mul_card_le_of_inf_eq_bot {A B C : Subgroup X} [Finite C] (hA : A ≤ C) (hB : B ≤ C)
    (h : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card C := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : A × B => (⟨p.1 * p.2, mul_mem (hA p.1.2) (hB p.2.2)⟩ : C)) fun p q hpq => ?_
  exact mul_injective_of_inf_eq_bot h (congrArg Subtype.val hpq)

theorem exists_mul_of_card_le {A B C : Subgroup X} [Finite C] (hA : A ≤ C) (hB : B ≤ C)
    (h : A ⊓ B = ⊥) (hcard : Nat.card C ≤ Nat.card A * Nat.card B) {c : X} (hc : c ∈ C) :
    ∃ a ∈ A, ∃ b ∈ B, c = a * b := by
  let f : A × B → C := fun p => ⟨p.1 * p.2, mul_mem (hA p.1.2) (hB p.2.2)⟩
  have hinj : Function.Injective f := fun p q hpq =>
    mul_injective_of_inf_eq_bot h (congrArg Subtype.val hpq)
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod]; exact hcard)
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨c, hc⟩
  exact ⟨a, a.2, b, b.2, (congrArg Subtype.val hab).symm⟩

theorem mem_map_conj_iff {A : Subgroup X} {c y : X} :
    y ∈ A.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * y * c ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro hy
    refine ⟨c⁻¹ * y * c, hy, ?_⟩
    simp [mul_assoc]

end CFSG.LargeExtraspecial.S5
