module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
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
public import Mathlib.Topology.Sheaves.Init

public section

open scoped Pointwise

namespace CFSG.QuasithinUnique.Setup.Offender

theorem solvable_normal_product {G : Type*} [Group G] (N M : Subgroup G) [N.Normal] [M.Normal]
    [Group.IsSolvable N] [Group.IsSolvable M] :
    ((N ⊔ M : Subgroup G) : Set G) = (N : Set G) * (M : Set G) ∧ (N ⊔ M).Normal ∧
      Group.IsSolvable (N ⊔ M : Subgroup G) :=
  ⟨Subgroup.normal_mul N M, inferInstance, CFSG.ABGLocalTools.isSolvable_sup_of_normal N M⟩

theorem solvableRadical_characterization (G : Type*) [Group G] [Finite G] :
    (CFSG.solvableRadical G).Characteristic ∧ Group.IsSolvable (CFSG.solvableRadical G) ∧
      (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N ≤ CFSG.solvableRadical G) ∧
      ∀ R : Subgroup G, R.Normal → Group.IsSolvable R →
        (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N ≤ R) →
        R = CFSG.solvableRadical G := by
  have hsolv : Group.IsSolvable (CFSG.solvableRadical G) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  have hnormal : (CFSG.solvableRadical G).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hmax : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N ≤ CFSG.solvableRadical G :=
    fun N hN hNs => le_sSup ⟨hN, hNs⟩
  refine ⟨?_, hsolv, hmax, fun R hRn hRs hR =>
    le_antisymm (hmax R hRn hRs) (hR _ hnormal hsolv)⟩
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  have hn : ((CFSG.solvableRadical G).map φ.toMonoidHom).Normal := hnormal.map _ φ.surjective
  have hs : Group.IsSolvable ((CFSG.solvableRadical G).map φ.toMonoidHom) :=
    Group.isSolvable_of_surjective
      (f := φ.toMonoidHom.subgroupMap (CFSG.solvableRadical G))
      (MonoidHom.subgroupMap_surjective _ _)
  exact hmax _ hn hs

end CFSG.QuasithinUnique.Setup.Offender
