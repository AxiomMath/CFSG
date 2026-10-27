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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

theorem smul_eq_of_mem_stabilizer_pair {G α : Type*} [Group G] [MulAction G α] {x y : α}
    (hxy : x ≠ y) {g : G} (hg : g ∈ MulAction.stabilizer G ({x, y} : Set α)) (hx : g • x = x) :
    g • y = y := by
  have hset : g • ({x, y} : Set α) = {x, y} := hg
  have hmem : g • y ∈ ({x, y} : Set α) := by
    have : g • y ∈ g • ({x, y} : Set α) :=
      Set.smul_mem_smul_set (show y ∈ ({x, y} : Set α) by simp)
    rwa [hset] at this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exfalso
    apply hxy
    apply MulAction.injective g
    change g • x = g • y
    rw [hx, h]
  · exact h

theorem card_stabilizer_pair {G α : Type*} [Group G] [MulAction G α] {x y : α} (hxy : x ≠ y)
    (τ : G) (hτx : τ • x = y) (hτy : τ • y = x) :
    Nat.card (MulAction.stabilizer G ({x, y} : Set α)) =
      2 * Nat.card ↥(MulAction.stabilizer G x ⊓ MulAction.stabilizer G y) := by
  let Z : Subgroup G := MulAction.stabilizer G ({x, y} : Set α)
  let L : Subgroup G := MulAction.stabilizer G x ⊓ MulAction.stabilizer G y
  change Nat.card ↥Z = 2 * Nat.card ↥L
  have hτZ : τ ∈ MulAction.stabilizer G ({x, y} : Set α) := by
    rw [MulAction.mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, hτx, hτy]
    exact Set.pair_comm y x
  have hτmap : (⟨τ, hτZ⟩ : ↥Z) • x = y := by
    rw [MulAction.subgroup_smul_def]
    exact hτx
  have horbit : MulAction.orbit ↥Z x = ({x, y} : Set α) := by
    apply Set.Subset.antisymm
    · intro a ha
      obtain ⟨z, rfl⟩ := MulAction.mem_orbit_iff.mp ha
      have hz : (z : G) • ({x, y} : Set α) = {x, y} := z.2
      have hmem : (z : G) • x ∈ ({x, y} : Set α) := by
        have hsub : (z : G) • x ∈ (z : G) • ({x, y} : Set α) :=
          Set.smul_mem_smul_set (show x ∈ ({x, y} : Set α) by simp)
        rwa [hz] at hsub
      simpa only [MulAction.subgroup_smul_def] using hmem
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact ⟨1, by simp⟩
      · exact MulAction.mem_orbit_iff.mpr ⟨⟨τ, hτZ⟩, hτmap⟩
  have hcard : (MulAction.orbit ↥Z x).ncard = 2 := by
    rw [horbit]
    exact Set.ncard_pair hxy
  have hindex : (MulAction.stabilizer ↥Z x).index = 2 := by
    rw [MulAction.index_stabilizer ↥Z x, hcard]
  have hZcard : Nat.card ↥Z = 2 * Nat.card (MulAction.stabilizer ↥Z x) := by
    have h := Subgroup.index_mul_card (H := MulAction.stabilizer ↥Z x)
    rw [hindex] at h
    exact h.symm
  have hZL : MulAction.stabilizer G x ⊓ Z = L := by
    change MulAction.stabilizer G x ⊓ MulAction.stabilizer G ({x, y} : Set α)
      = MulAction.stabilizer G x ⊓ MulAction.stabilizer G y
    ext g
    simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨hx, hZg⟩
      exact ⟨hx, smul_eq_of_mem_stabilizer_pair hxy (MulAction.mem_stabilizer_iff.mpr hZg) hx⟩
    · rintro ⟨hx, hy⟩
      refine ⟨hx, ?_⟩
      rw [Set.smul_set_insert, Set.smul_set_singleton, hx, hy]
  have hLcard : Nat.card (MulAction.stabilizer ↥Z x) = Nat.card ↥L := by
    rw [← MulAction.stabilizer_subgroupOf Z x]
    rw [← Subgroup.card_subtype Z ((MulAction.stabilizer G x).subgroupOf Z)]
    rw [Subgroup.subgroupOf_map_subtype]
    rw [hZL]
  rw [hZcard, hLcard]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
