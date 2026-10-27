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

namespace CFSG.ClassicalInvolution.Asc77

theorem sq_eq_of_rel_gen {A : Type*} [Group A] (hc : ∀ x y : A, x * y = y * x) {za zb w s : A}
    (h : za * (w * s) = (zb * za) * (w⁻¹ * s)) : w * w = zb := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hc }
  have h1 : za * s * (w * w) = za * s * zb := by
    calc za * s * (w * w) = (za * (w * s)) * w := by ac_rfl
      _ = ((zb * za) * (w⁻¹ * s)) * w := by rw [h]
      _ = (za * s) * zb * (w⁻¹ * w) := by ac_rfl
      _ = za * s * zb := by rw [inv_mul_cancel, mul_one]
  exact mul_left_cancel h1

namespace Thompson

theorem sq_eq_of_conj_gen {G : Type} [Group G] {W : Subgroup G}
    (hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {r u za zb w s : G} (hza : za ∈ W) (hzb : zb ∈ W)
    (hw : w ∈ W) (hs : s ∈ W) (hu : u = za * (w * s)) (hru : r * u * r⁻¹ = u)
    (hrza : r * za * r⁻¹ = zb * za) (hrw : r * w * r⁻¹ = w⁻¹) (hrs : r * s * r⁻¹ = s) :
    w * w = zb := by
  have hru' : r * (za * (w * s)) * r⁻¹ = za * (w * s) := by rw [← hu]; exact hru
  have h1 : za * (w * s) = (zb * za) * (w⁻¹ * s) := by
    calc za * (w * s) = r * (za * (w * s)) * r⁻¹ := hru'.symm
      _ = (r * za * r⁻¹) * ((r * w * r⁻¹) * (r * s * r⁻¹)) := by group
      _ = (zb * za) * (w⁻¹ * s) := by rw [hrza, hrw, hrs]
  have hc' : ∀ x y : ↥W, x * y = y * x := fun x y => Subtype.ext (hcomm x x.2 y y.2)
  have := sq_eq_of_rel_gen hc' (za := ⟨za, hza⟩) (zb := ⟨zb, hzb⟩) (w := ⟨w, hw⟩) (s := ⟨s, hs⟩)
    (Subtype.ext h1)
  exact congrArg Subtype.val this
end Thompson

end CFSG.ClassicalInvolution.Asc77
