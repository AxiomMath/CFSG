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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.EvenSporadicStandard.M24Std.CResH2

open Equiv

private def k1 : Perm (Fin 8) := swap 0 1 * swap 2 3

private def k2 : Perm (Fin 8) := swap 0 2 * swap 1 3

private def k3 : Perm (Fin 8) := swap 4 5 * swap 6 7

private def k4 : Perm (Fin 8) := swap 4 6 * swap 5 7

private def T4 (x : Fin 4 → ZMod 2) : Perm (Fin 8) :=
  k1 ^ (x 0).val * k2 ^ (x 1).val * k3 ^ (x 2).val * k4 ^ (x 3).val

private theorem T4_add : ∀ x y : Fin 4 → ZMod 2, T4 (x + y) = T4 x * T4 y := by
  unfold T4 k1 k2 k3 k4
  decide +revert

private theorem T4_sign : ∀ x : Fin 4 → ZMod 2, Perm.sign (T4 x) = 1 := by
  unfold T4 k1 k2 k3 k4
  decide +revert

private theorem T4_inj : ∀ x : Fin 4 → ZMod 2, T4 x = 1 → x = 0 := by
  unfold T4 k1 k2 k3 k4
  decide +revert

private def psi4 : Multiplicative (Fin 4 → ZMod 2) →* alternatingGroup (Fin 8) :=
  MonoidHom.mk' (fun x => ⟨T4 (Multiplicative.toAdd x), Perm.mem_alternatingGroup.2 (T4_sign _)⟩)
    (fun _ _ => Subtype.ext (T4_add _ _))

theorem exists_hom_rank_four :
    ∃ ψ : Multiplicative (Fin 4 → ZMod 2) →* alternatingGroup (Fin 8), Function.Injective ψ := by
  refine ⟨psi4, (injective_iff_map_eq_one _).2 fun x hx => ?_⟩
  have h : T4 (Multiplicative.toAdd x) = 1 := congrArg Subtype.val hx
  exact Multiplicative.toAdd.injective (T4_inj _ h)

private def a1 : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

private def a2 : Perm (Fin 8) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7

private def a3 : Perm (Fin 8) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

private def T3 (x : Fin 3 → ZMod 2) : Perm (Fin 8) :=
  a1 ^ (x 0).val * a2 ^ (x 1).val * a3 ^ (x 2).val

private theorem T3_add : ∀ x y : Fin 3 → ZMod 2, T3 (x + y) = T3 x * T3 y := by
  unfold T3 a1 a2 a3
  decide +revert

private theorem T3_sign : ∀ x : Fin 3 → ZMod 2, Perm.sign (T3 x) = 1 := by
  unfold T3 a1 a2 a3
  decide +revert

private theorem T3_inj : ∀ x : Fin 3 → ZMod 2, T3 x = 1 → x = 0 := by
  unfold T3 a1 a2 a3
  decide +revert

private def linMaps : Fin 7 → Perm (Fin 8) :=
  ![1, swap 1 2 * swap 5 6, swap 1 4 * swap 3 6, swap 1 3 * swap 5 7, swap 1 5 * swap 3 7,
    (swap 2 6 * swap 3 7) * (swap 1 2 * swap 5 6), swap 1 7 * swap 3 5]

private theorem linMaps_sign : ∀ i : Fin 7, Perm.sign (linMaps i) = 1 := by
  unfold linMaps
  decide +revert

private theorem linMaps_conj : ∀ y : Fin 3 → ZMod 2, y ≠ 0 →
    ∃ i : Fin 7, linMaps i * a1 * (linMaps i)⁻¹ = T3 y := by
  unfold linMaps T3 a1 a2 a3
  decide +revert

private def psi3 : Multiplicative (Fin 3 → ZMod 2) →* alternatingGroup (Fin 8) :=
  MonoidHom.mk' (fun x => ⟨T3 (Multiplicative.toAdd x), Perm.mem_alternatingGroup.2 (T3_sign _)⟩)
    (fun _ _ => Subtype.ext (T3_add _ _))

theorem exists_hom_translations :
    ∃ ψ : Multiplicative (Fin 3 → ZMod 2) →* alternatingGroup (Fin 8), Function.Injective ψ ∧
      ∀ x y : Multiplicative (Fin 3 → ZMod 2), x ≠ 1 → y ≠ 1 →
        ∃ g : alternatingGroup (Fin 8), g * ψ x * g⁻¹ = ψ y := by
  refine ⟨psi3, (injective_iff_map_eq_one _).2 fun x hx => ?_, ?_⟩
  · have h : T3 (Multiplicative.toAdd x) = 1 := congrArg Subtype.val hx
    exact Multiplicative.toAdd.injective (T3_inj _ h)
  · intro x y hx hy
    have hx0 : Multiplicative.toAdd x ≠ 0 := fun h => hx (Multiplicative.toAdd.injective h)
    have hy0 : Multiplicative.toAdd y ≠ 0 := fun h => hy (Multiplicative.toAdd.injective h)
    obtain ⟨i, hi⟩ := linMaps_conj _ hx0
    obtain ⟨j, hj⟩ := linMaps_conj _ hy0
    let gi : alternatingGroup (Fin 8) := ⟨linMaps i, Perm.mem_alternatingGroup.2 (linMaps_sign i)⟩
    let gj : alternatingGroup (Fin 8) := ⟨linMaps j, Perm.mem_alternatingGroup.2 (linMaps_sign j)⟩
    refine ⟨gj * gi⁻¹, Subtype.ext ?_⟩
    show linMaps j * (linMaps i)⁻¹ * T3 (Multiplicative.toAdd x) * (linMaps j * (linMaps i)⁻¹)⁻¹ =
      T3 (Multiplicative.toAdd y)
    rw [← hi, ← hj]
    group

end CFSG.EvenSporadicStandard.M24Std.CResH2
