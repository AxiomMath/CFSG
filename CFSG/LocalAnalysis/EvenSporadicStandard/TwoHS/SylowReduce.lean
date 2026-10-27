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

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup
open scoped Pointwise

theorem exists_conj_mem_of_dvd_card {G : Type*} [Group G] [Finite G] (V : Subgroup G)
    (hV : 2 ^ (Nat.card G).factorization 2 ∣ Nat.card V) {g : G}
    (hg : IsPGroup 2 (zpowers g)) : ∃ x : G, x * g * x⁻¹ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := V) 2 hV
  have hP : Nat.card (P₀.map V.subtype) = 2 ^ (Nat.card G).factorization 2 := by
    rw [Subgroup.card_map_of_injective V.subtype_injective, hP₀]
  let SP : Sylow 2 G := Sylow.ofCard (P₀.map V.subtype) hP
  obtain ⟨Q, hQ⟩ := hg.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G SP Q
  have hgQ : g ∈ (Q : Set G) := hQ (mem_zpowers g)
  rw [← hx, Sylow.coe_smul, Set.mem_smul_set] at hgQ
  obtain ⟨s, hs, hsg⟩ := hgQ
  have hsP : s ∈ P₀.map V.subtype := hs
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hsP
  refine ⟨x⁻¹, ?_⟩
  have : x * (v : G) * x⁻¹ = g := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using hsg
  rw [← this]
  have e : x⁻¹ * (x * (v : G) * x⁻¹) * (x⁻¹)⁻¹ = (v : G) := by group
  rw [e]
  exact v.2

theorem isPGroup_zpowers_of_pow_four_eq_one {G : Type*} [Group G] {g : G} (h : g ^ 4 = 1) :
    IsPGroup 2 (zpowers g) := by
  have h1 : orderOf g ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

end CFSG.EvenSporadicStandard.TwoHS
