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

namespace CFSG.ClassicalInvolution

theorem exists_conj_mem_of_sylow {G : Type*} [Group G] [Finite G] (S : Subgroup G)
    (hS : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.index) {u : G} (hu : orderOf u = 2) :
    ∃ c : G, c * u * c⁻¹ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 G := hS.toSylow hidx
  have hz : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S'
  refine ⟨g, ?_⟩
  have h1 : u ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers u)
  have h2 : g * u * g⁻¹ ∈ ((g • Q : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨u, h1, rfl⟩
  rw [hg] at h2
  exact h2

variable {M : Type*} [Group M]

theorem cover_of_sylow (H S : Subgroup M) [Finite H] (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ (S.subgroupOf H).index) (r : M)
    (hSr : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ H, s = c * r * c⁻¹) :
    ∀ u ∈ H, orderOf u = 2 → ∃ c ∈ H, u = c * r * c⁻¹ := by
  intro u hu ho
  have hSp : IsPGroup 2 (S.subgroupOf H) := hS.comap_of_injective H.subtype H.subtype_injective
  have ho' : orderOf (⟨u, hu⟩ : H) = 2 := by rw [← ho, ← Subgroup.orderOf_coe]
  obtain ⟨c₁, hc₁⟩ := exists_conj_mem_of_sylow (S.subgroupOf H) hSp hidx ho'
  have hc₁S : (c₁ : M) * u * (c₁ : M)⁻¹ ∈ S := by
    have := Subgroup.mem_subgroupOf.1 hc₁
    simpa using this
  have hord : orderOf ((c₁ : M) * u * (c₁ : M)⁻¹) = 2 := by
    rw [← ho]
    exact MulEquiv.orderOf_eq (MulAut.conj (c₁ : M)) u
  obtain ⟨c₂, hc₂, he⟩ := hSr _ hc₁S hord
  refine ⟨(c₁ : M)⁻¹ * c₂, H.mul_mem (H.inv_mem c₁.2) hc₂, ?_⟩
  calc u = (c₁ : M)⁻¹ * ((c₁ : M) * u * (c₁ : M)⁻¹) * (c₁ : M) := by group
    _ = (c₁ : M)⁻¹ * (c₂ * r * c₂⁻¹) * (c₁ : M) := by rw [he]
    _ = ((c₁ : M)⁻¹ * c₂) * r * ((c₁ : M)⁻¹ * c₂)⁻¹ := by group

end CFSG.ClassicalInvolution
