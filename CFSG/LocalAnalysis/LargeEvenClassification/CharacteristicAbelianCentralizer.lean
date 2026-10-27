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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem subgroup_centralizer_top_eq_center {Ambient : Type groupUniverse} [Group Ambient] :
    Subgroup.centralizer ((⊤ : Subgroup Ambient) : Set Ambient) = Subgroup.center Ambient := by
  ext source
  constructor
  · intro hsource
    exact Subgroup.mem_center_iff.mpr (fun actor => Subgroup.mem_centralizer_iff.mp hsource actor (by trivial))
  · intro hsource
    exact Subgroup.mem_centralizer_iff.mpr (fun actor _ => Subgroup.mem_center_iff.mp hsource actor)

theorem characteristic_abelian_central_nilpotency_class_two
    {Ambient : Type groupUniverse} [Group Ambient] [Group.IsNilpotent Ambient]
    (hcentral : ∀ Abelian : Subgroup Ambient, Abelian.Characteristic → IsMulCommutative Abelian →
      Abelian ≤ Subgroup.center Ambient) : Group.nilpotencyClass Ambient ≤ 2 := by
  have hdescend : ∀ count : ℕ, (⊤ : Subgroup Ambient).lowerCentralSeries (count + 2) = ⊥ →
      (⊤ : Subgroup Ambient).lowerCentralSeries 2 = ⊥ := by
    intro count
    induction count with
    | zero => exact id
    | succ count induction =>
        intro hzero
        let Previous := (⊤ : Subgroup Ambient).lowerCentralSeries (count + 1)
        let Last := (⊤ : Subgroup Ambient).lowerCentralSeries (count + 2)
        have hlastCentral : Last ≤ Subgroup.center Ambient := by
          rw [← subgroup_centralizer_top_eq_center]
          apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          change ⁅(⊤ : Subgroup Ambient).lowerCentralSeries (count + 2), ⊤⁆ = ⊥
          rw [← Subgroup.lowerCentralSeries_succ]
          exact hzero
        have hlastCommutes : ⁅Last, (⊤ : Subgroup Ambient)⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            ((subgroup_centralizer_top_eq_center (Ambient := Ambient)).symm ▸ hlastCentral)
        have hpreviousTop : ⁅Previous, (⊤ : Subgroup Ambient)⁆ = Last :=
          (Subgroup.lowerCentralSeries_succ ⊤ (count + 1)).symm
        have htopPrevious : ⁅(⊤ : Subgroup Ambient), Previous⁆ = Last :=
          (Subgroup.commutator_comm _ _).trans hpreviousTop
        have hrotateFirst : (⁅⁅(⊤ : Subgroup Ambient), Previous⁆,
            (⊤ : Subgroup Ambient)⁆ : Subgroup Ambient) = ⊥ := by
          rw [htopPrevious]
          exact hlastCommutes
        have hrotateSecond : (⁅⁅Previous, (⊤ : Subgroup Ambient)⁆,
            (⊤ : Subgroup Ambient)⁆ : Subgroup Ambient) = ⊥ := by
          rw [hpreviousTop]
          exact hlastCommutes
        have hderivedCommutes : (⁅⁅(⊤ : Subgroup Ambient), (⊤ : Subgroup Ambient)⁆,
            Previous⁆ : Subgroup Ambient) = ⊥ :=
          Subgroup.commutator_commutator_eq_bot_of_rotate hrotateFirst hrotateSecond
        have hpreviousDerived : Previous ≤ ⁅(⊤ : Subgroup Ambient), (⊤ : Subgroup Ambient)⁆ := by
          have hle := Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup Ambient)
            (show 1 ≤ count + 1 by omega)
          have hone : (⊤ : Subgroup Ambient).lowerCentralSeries 1 = ⁅(⊤ : Subgroup Ambient),
              (⊤ : Subgroup Ambient)⁆ := by
            simpa only [Subgroup.lowerCentralSeries_zero] using
              Subgroup.lowerCentralSeries_succ (⊤ : Subgroup Ambient) 0
          exact hle.trans (le_of_eq hone)
        have hpreviousAbelian : IsMulCommutative Previous :=
          Subgroup.le_centralizer_iff_isMulCommutative.mp
            (hpreviousDerived.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hderivedCommutes))
        have hpreviousCentral := hcentral Previous inferInstance hpreviousAbelian
        have hlastZero : Last = ⊥ := by
          rw [← hpreviousTop]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            ((subgroup_centralizer_top_eq_center (Ambient := Ambient)).symm ▸ hpreviousCentral)
        exact induction hlastZero
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  have hlast := Subgroup.lowerCentralSeries_nilpotencyClass (G := Ambient)
  by_cases hsmall : Group.nilpotencyClass Ambient ≤ 2
  · exact le_antisymm ((Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup Ambient) hsmall).trans
      (le_of_eq hlast)) bot_le
  · obtain ⟨count, hcount⟩ := Nat.exists_eq_add_of_le (show 2 ≤ Group.nilpotencyClass Ambient by omega)
    have heq : Group.nilpotencyClass Ambient = count + 2 := by omega
    exact hdescend count (heq ▸ hlast)

end CFSG.LargeEvenClassification.Helpers
