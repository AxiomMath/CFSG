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

namespace T7L

variable {G : Type*} [Group G]

theorem map_centralizer_conj_le {k k' : G} (c : G) (hk : k' = c * k * c⁻¹) :
    (Subgroup.centralizer ({k} : Set G)).map (MulAut.conj c).toMonoidHom ≤
      Subgroup.centralizer ({k'} : Set G) := by
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w ∈ Subgroup.centralizer ({k} : Set G) := hw
  rw [Subgroup.mem_centralizer_singleton_iff] at hw'
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hk]
  calc c * w * c⁻¹ * (c * k * c⁻¹) = c * (w * k) * c⁻¹ := by group
    _ = c * (k * w) * c⁻¹ := by rw [hw']
    _ = c * k * c⁻¹ * (c * w * c⁻¹) := by group

theorem top_le_sup_of_conj {x0 u0 x y : G} (c : G) (hx : x = c * x0 * c⁻¹)
    (hy : y = c * u0 * c⁻¹)
    (h : (⊤ : Subgroup G) ≤
      Subgroup.centralizer ({x0} : Set G) ⊔ Subgroup.centralizer ({u0} : Set G)) :
    (⊤ : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.centralizer ({y} : Set G) := by
  intro z _
  have hz : c⁻¹ * z * c ∈
      Subgroup.centralizer ({x0} : Set G) ⊔ Subgroup.centralizer ({u0} : Set G) := h trivial
  have h2 : (Subgroup.centralizer ({x0} : Set G) ⊔ Subgroup.centralizer ({u0} : Set G)).map
      (MulAut.conj c).toMonoidHom ≤
        Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (map_centralizer_conj_le c hx) (map_centralizer_conj_le c hy)
  have := h2 ⟨_, hz, rfl⟩
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem e4_goal_of_top_le (x y z : G)
    (h : (⊤ : Subgroup G) ≤
      Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.centralizer ({y} : Set G)) :
    (⊤ : Subgroup G) = Subgroup.center G ⊔ (Subgroup.centralizer ({x} : Set G) ⊔
      Subgroup.centralizer ({y} : Set G) ⊔ Subgroup.centralizer ({z} : Set G)) :=
  le_antisymm (h.trans (le_sup_left.trans le_sup_right)) le_top

theorem centralizer_le_of_mul_central {x z : G} (hz : z ∈ Subgroup.center G) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({x * z} : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
  have hzw := Subgroup.mem_center_iff.mp hz w
  calc w * (x * z) = (w * x) * z := by group
    _ = (x * w) * z := by rw [hw]
    _ = x * (w * z) := by group
    _ = x * (z * w) := by rw [hzw]
    _ = (x * z) * w := by group

theorem centralizer_mul_central_le {x z : G} (hz : z ∈ Subgroup.center G) :
    Subgroup.centralizer ({x * z} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
  have hzw := Subgroup.mem_center_iff.mp hz w
  have h1 : (w * x) * z = (x * w) * z := by
    calc (w * x) * z = w * (x * z) := by group
      _ = (x * z) * w := hw
      _ = x * (z * w) := by group
      _ = x * (w * z) := by rw [← hzw]
      _ = (x * w) * z := by group
  exact mul_right_cancel h1

end T7L

end CFSG.ClassicalInvolution.Asc77
