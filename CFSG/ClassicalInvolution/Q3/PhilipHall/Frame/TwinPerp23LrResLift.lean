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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc.Res

open scoped commutatorElement

theorem exists_perfect_lift {K L : Type*} [Group K] [Group L] [Finite K] (φ : K →* L)
    (hker : φ.ker ≤ Subgroup.center K) (g : K) {Q : Subgroup L} (hQ : Group.IsPerfect Q)
    (hQr : Q ≤ φ.range) (hQg : ∀ x ∈ Q, x * φ g = φ g * x) :
    ∃ S : Subgroup K, Group.IsPerfect S ∧ (∀ s ∈ S, s * g = g * s) ∧ S.map φ = Q := by
  classical
  have hne : ({S : Subgroup K | S.map φ = Q} : Set (Subgroup K)).Nonempty :=
    ⟨Q.comap φ, by
      change (Q.comap φ).map φ = Q
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.mpr hQr⟩
  obtain ⟨S, hS, hmin⟩ := (wellFounded_lt (α := Subgroup K)).has_min _ hne
  replace hS : S.map φ = Q := hS
  have hQc : ⁅Q, Q⁆ = Q := Subgroup.commutator_eq_self
  have hcomm_le : ⁅S, S⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have hSS : ⁅S, S⁆ = S := by
    by_contra hne'
    refine hmin ⁅S, S⁆ ?_ (lt_of_le_of_ne hcomm_le hne')
    change (⁅S, S⁆ : Subgroup K).map φ = Q
    rw [Subgroup.map_commutator, hS, hQc]
  have hSZ : ⁅S, Subgroup.zpowers g⁆ ≤ Subgroup.center K := by
    refine le_trans ?_ hker
    rw [← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, hS, MonoidHom.map_zpowers,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (hQg x hx).symm n)).eq
  have hbot1 : ⁅⁅S, Subgroup.zpowers g⁆, S⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hSZ.trans (Subgroup.center_le_centralizer _))
  have hbot2 : ⁅⁅Subgroup.zpowers g, S⁆, S⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (Subgroup.zpowers g) S]
    exact hbot1
  have hbot3 : ⁅⁅S, S⁆, Subgroup.zpowers g⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hbot1 hbot2
  rw [hSS] at hbot3
  refine ⟨S, Subgroup.isPerfect_iff.mpr hSS, fun s hs => ?_, hS⟩
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot3 hs
  exact (Subgroup.mem_centralizer_iff.mp this g (Subgroup.mem_zpowers g)).symm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc.Res
