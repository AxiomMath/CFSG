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
public import Mathlib.GroupTheory.Transfer
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

namespace CFSG.LargeExtraspecial.S63

open Subgroup
open scoped commutatorElement

section Cube

variable {G : Type*} [Group G]

theorem conj_commutatorElement_eq (y u v : G) :
    y * ⁅u, v⁆ * y⁻¹ = ⁅y * u * y⁻¹, y * v * y⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_of_mem_center {c : G} (hc : c ∈ center G) (y : G) : y * c * y⁻¹ = c := by
  rw [mem_center_iff.mp hc y, mul_inv_cancel_right]

theorem commutatorElement_mul_of_mem_center {u v w : G} (h : ⁅u, w⁆ ∈ center G) :
    ⁅u, v * w⁆ = ⁅u, v⁆ * ⁅u, w⁆ := by
  have e : ⁅u, v * w⁆ = ⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, conj_eq_of_mem_center h]

theorem commutatorElement_center_mul {u c w : G} (hc : c ∈ center G) :
    ⁅u, c * w⁆ = ⁅u, w⁆ := by
  have e : ⁅u, c * w⁆ = u * (c * (w * u⁻¹ * w⁻¹)) * c⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, ← mem_center_iff.mp hc, commutatorElement_def]
  group

theorem commutator_eq_one_of_cube {x₁ x₂ x₃ y : G} (h₂ : y * x₁ * y⁻¹ = x₂)
    (h₃ : y * x₂ * y⁻¹ = x₃) (h12 : ⁅x₁, x₂⁆ ∈ center G) (h13 : ⁅x₁, x₃⁆ ∈ center G)
    (h23 : ⁅x₂, x₃⁆ ∈ center G) (hrel : y * x₃ * y⁻¹ * (x₂ * x₁)⁻¹ ∈ center G) :
    ⁅x₁, x₂⁆ = 1 ∧ ⁅x₁, x₃⁆ = 1 ∧ ⁅x₂, x₃⁆ = 1 := by
  set c := y * x₃ * y⁻¹ * (x₂ * x₁)⁻¹ with hc
  have hy3 : y * x₃ * y⁻¹ = c * (x₂ * x₁) := by rw [hc]; group
  have had : ⁅x₁, x₂⁆ = ⁅x₂, x₃⁆ := by
    calc ⁅x₁, x₂⁆ = y * ⁅x₁, x₂⁆ * y⁻¹ := (conj_eq_of_mem_center h12 y).symm
      _ = ⁅x₂, x₃⁆ := by rw [conj_commutatorElement_eq, h₂, h₃]
  have hba : ⁅x₁, x₃⁆ = ⁅x₁, x₂⁆⁻¹ := by
    have h21 : ⁅x₂, x₁⁆ ∈ center G := by
      rw [← commutatorElement_inv]
      exact inv_mem h12
    calc ⁅x₁, x₃⁆ = y * ⁅x₁, x₃⁆ * y⁻¹ := (conj_eq_of_mem_center h13 y).symm
      _ = ⁅x₂, c * (x₂ * x₁)⁆ := by rw [conj_commutatorElement_eq, h₂, hy3]
      _ = ⁅x₂, x₂⁆ * ⁅x₂, x₁⁆ := by
        rw [commutatorElement_center_mul hrel, commutatorElement_mul_of_mem_center h21]
      _ = ⁅x₁, x₂⁆⁻¹ := by rw [commutatorElement_self, one_mul, commutatorElement_inv]
  have hdd : ⁅x₂, x₃⁆ = ⁅x₂, x₃⁆⁻¹ * ⁅x₁, x₃⁆⁻¹ := by
    have h31 : ⁅x₃, x₁⁆ ∈ center G := by
      rw [← commutatorElement_inv]
      exact inv_mem h13
    calc ⁅x₂, x₃⁆ = y * ⁅x₂, x₃⁆ * y⁻¹ := (conj_eq_of_mem_center h23 y).symm
      _ = ⁅x₃, c * (x₂ * x₁)⁆ := by rw [conj_commutatorElement_eq, h₃, hy3]
      _ = ⁅x₃, x₂⁆ * ⁅x₃, x₁⁆ := by
        rw [commutatorElement_center_mul hrel, commutatorElement_mul_of_mem_center h31]
      _ = ⁅x₂, x₃⁆⁻¹ * ⁅x₁, x₃⁆⁻¹ := by rw [commutatorElement_inv, commutatorElement_inv]
  rw [hba, had, inv_inv, inv_mul_cancel] at hdd
  refine ⟨had.trans hdd, ?_, hdd⟩
  rw [hba, had, hdd, inv_one]

end Cube

section Transfer

theorem pow_index_mem_commutator {G : Type*} [Group G] [Finite G] (hG : commutator G = ⊤)
    (H : Subgroup G) {z : G} (hz : z ∈ center G) : z ^ H.index ∈ ⁅H, H⁆ := by
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    rw [mem_center_iff.mp (pow_mem hz k) g₀⁻¹, inv_mul_cancel_right]
  have h1 := MonoidHom.transfer_eq_pow (Abelianization.of : H →* Abelianization H) z key
  have h2 : z ∈ (Abelianization.of : H →* Abelianization H).transfer.ker :=
    Abelianization.commutator_subset_ker _ (by rw [hG]; exact mem_top z)
  rw [MonoidHom.mem_ker, h1, ← MonoidHom.mem_ker, Abelianization.ker_of] at h2
  have h3 := mem_map_of_mem H.subtype h2
  rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h3

end Transfer

section Normalizer

variable {G : Type*} [Group G]

theorem commutator_mem_of_le_normalizer {A B : Subgroup G}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAB : A ≤ normalizer (B : Set G)) {g h : G}
    (hg : g ∈ B ⊔ A) (hh : h ∈ B ⊔ A) : ⁅g, h⁆ ∈ B := by
  set T := B ⊔ A with hT
  have hBT : B ≤ T := le_sup_left
  have hAT : A ≤ T := le_sup_right
  have hTN : T ≤ normalizer (B : Set G) := sup_le le_normalizer hAB
  have : (B.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hBT).mpr hTN
  have htop : B.subgroupOf T ⊔ A.subgroupOf T = ⊤ := by
    rw [← subgroupOf_sup hBT hAT, ← hT, subgroupOf_self]
  have hdec : ∀ t : T, ∃ b ∈ B.subgroupOf T, ∃ a ∈ A.subgroupOf T, b * a = t := by
    intro t
    have ht : t ∈ ((B.subgroupOf T ⊔ A.subgroupOf T : Subgroup T) : Set T) := by
      rw [htop]
      exact Set.mem_univ t
    rw [normal_mul] at ht
    obtain ⟨b, hb, a, ha, hab⟩ := Set.mem_mul.mp ht
    exact ⟨b, hb, a, ha, hab⟩
  set ρ := QuotientGroup.mk' (B.subgroupOf T) with hρ
  have hρb : ∀ b ∈ B.subgroupOf T, ρ b = 1 := fun b hb => (QuotientGroup.eq_one_iff b).mpr hb
  obtain ⟨b₁, hb₁, a₁, ha₁, e₁⟩ := hdec ⟨g, hg⟩
  obtain ⟨b₂, hb₂, a₂, ha₂, e₂⟩ := hdec ⟨h, hh⟩
  have hc : ρ ⁅(⟨g, hg⟩ : T), ⟨h, hh⟩⁆ = 1 := by
    have h12 : a₁ * a₂ = a₂ * a₁ :=
      Subtype.ext (hA _ (mem_subgroupOf.mp ha₁) _ (mem_subgroupOf.mp ha₂))
    rw [← e₁, ← e₂, map_commutatorElement, map_mul, map_mul, hρb b₁ hb₁, hρb b₂ hb₂, one_mul,
      one_mul, ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr h12, map_one]
  rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hc
  exact hc

end Normalizer

end CFSG.LargeExtraspecial.S63
