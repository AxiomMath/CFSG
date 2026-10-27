module

public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Orthogonality
public import Mathlib.Algebra.Group.ConjFinite
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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG

namespace Burnside

open scoped BigOperators

universe u

private theorem ClassFun.isIntegral_action_conjClassIndicator
    {G : Type u} [Group G] [Fintype G] (x : G) (V : FDRep ℂ G) :
    IsIntegral ℤ
      (ClassFun.action (ClassFun.conjClassIndicator ℂ x⁻¹) V) := by
  classical
  let z : MonoidAlgebra ℤ G :=
    ∑ g : G, MonoidAlgebra.single g⁻¹
      (if IsConj g x⁻¹ then (1 : ℤ) else 0)
  let Φ : MonoidAlgebra ℤ G →ₐ[ℤ] Module.End ℂ V :=
    (MonoidAlgebra.lift ℤ (Module.End ℂ V) G) V.ρ
  have hz : IsIntegral ℤ z := IsIntegral.of_finite ℤ z
  have hmap : Φ z =
      ClassFun.action (ClassFun.conjClassIndicator ℂ x⁻¹) V := by
    simp only [z, Φ, map_sum, MonoidAlgebra.lift_single, ClassFun.action]
    apply Finset.sum_congr rfl
    intro g hg
    by_cases hconj : IsConj g x⁻¹
    · simp [ClassFun.conjClassIndicator_apply]
    · simp [ClassFun.conjClassIndicator_apply]
  rw [← hmap]
  exact hz.map Φ

theorem ClassFun.isIntegral_scalar_of_action_conjClassIndicator_eq
    {G : Type u} [Group G] [Fintype G] (x : G) (V : FDRep ℂ G)
    [Nontrivial V] (lambda : ℂ)
    (hscalar : ClassFun.action (ClassFun.conjClassIndicator ℂ x⁻¹) V =
      lambda • (LinearMap.id : Module.End ℂ V)) :
    IsIntegral ℤ lambda := by
  have hinj : Function.Injective
      (algebraMap ℂ (Module.End ℂ V)) := by
    intro a b hab
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have habv := DFunLike.congr_fun hab v
    change a • v = b • v at habv
    have hsub : (a - b) • v = 0 := by
      rw [sub_smul, habv, sub_self]
    rcases smul_eq_zero.mp hsub with hab | hv0
    · exact sub_eq_zero.mp hab
    · exact (hv hv0).elim
  apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℂ (Module.End ℂ V)) hinj).mp
  have hmap : (algebraMap ℂ (Module.End ℂ V)) lambda =
      lambda • (LinearMap.id : Module.End ℂ V) := by
    ext v
    simp [Algebra.algebraMap_eq_smul_one]
  change IsIntegral ℤ ((algebraMap ℂ (Module.End ℂ V)) lambda)
  rw [hmap, ← hscalar]
  exact ClassFun.isIntegral_action_conjClassIndicator x V

end Burnside

end CFSG
