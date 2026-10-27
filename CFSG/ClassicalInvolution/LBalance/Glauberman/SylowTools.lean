module

public import CFSG.GroupTheory.ABGLocalTools.Basic
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

namespace CFSG.ClassicalInvolution.GlaubermanAut

open CFSG.ABGLocalTools
open scoped Pointwise

section SylowTools

variable {Ω : Type*} [Group Ω] {p : ℕ}

theorem mem_smul_sylow {H : Type*} [Group H] (Q : Sylow p H) (h x : H) :
    x ∈ (h • Q : Sylow p H) ↔ h⁻¹ * x * h ∈ Q := by
  have : x ∈ ((h • Q : Sylow p H) : Subgroup H) ↔ x ∈ MulAut.conj h • (Q : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
  rw [show (x ∈ (h • Q : Sylow p H)) ↔ x ∈ ((h • Q : Sylow p H) : Subgroup H) from Iff.rfl, this,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp
  exact Iff.rfl

variable [Fact p.Prime] [Finite Ω]

omit [Fact p.Prime] [Finite Ω] in
theorem exists_isSylowOf_ge {R H : Subgroup Ω} (hR : IsPGroup p R) (hRH : R ≤ H) :
    ∃ T : Subgroup Ω, R ≤ T ∧ IsSylowOf p T H := by
  obtain ⟨Q, hQ⟩ := (hR.comap_subtype (K := H)).exists_le_sylow
  exact ⟨Q.map H.subtype, fun x hx => ⟨⟨x, hRH hx⟩, hQ hx, rfl⟩, Q, rfl⟩

theorem isSylowOf_exists_conj {T₁ T₂ H : Subgroup Ω} (h₁ : IsSylowOf p T₁ H)
    (h₂ : IsSylowOf p T₂ H) : ∃ x ∈ H, ∀ y : Ω, y ∈ T₂ ↔ x⁻¹ * y * x ∈ T₁ := by
  obtain ⟨Q₁, rfl⟩ := h₁
  obtain ⟨Q₂, rfl⟩ := h₂
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H Q₁ Q₂
  refine ⟨h, h.2, fun y => ?_⟩
  constructor
  · rintro ⟨y', hy', rfl⟩
    rw [← hh] at hy'
    exact ⟨_, (mem_smul_sylow Q₁ h y').1 hy', by simp⟩
  · rintro ⟨y', hy', hy⟩
    have hyH : y ∈ H := by
      have : (h : Ω)⁻¹ * y * h = y' := hy.symm
      have h1 : y = h * y' * (h : Ω)⁻¹ := by rw [← this]; group
      rw [h1]
      exact H.mul_mem (H.mul_mem h.2 y'.2) (H.inv_mem h.2)
    refine ⟨⟨y, hyH⟩, ?_, rfl⟩
    rw [← hh]
    refine (mem_smul_sylow Q₁ h ⟨y, hyH⟩).2 ?_
    have : (h : H)⁻¹ * ⟨y, hyH⟩ * h = y' := Subtype.ext hy.symm
    rw [this]
    exact hy'

theorem isSylowOf_card_le {T R H : Subgroup Ω} (hT : IsSylowOf p T H) (hR : IsPGroup p R)
    (hRH : R ≤ H) : Nat.card R ≤ Nat.card T := by
  obtain ⟨T', hRT', hT'⟩ := exists_isSylowOf_ge hR hRH
  rw [hT.card_eq, ← hT'.card_eq]
  exact Subgroup.card_le_of_le hRT'

omit [Fact p.Prime] [Finite Ω] in
theorem isSylowOf_le_of_le_normalizer {T N H : Subgroup Ω} (hT : IsSylowOf p T H)
    (hNp : IsPGroup p N) (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set Ω)) : N ≤ T := by
  obtain ⟨Q, rfl⟩ := hT
  have hN' : (Subgroup.comap H.subtype N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hHN
  have h1 : N.subgroupOf H ≤ Q := (hNp.comap_subtype (K := H)).le_sylow_of_normal Q
  intro x hx
  exact ⟨⟨x, hNH hx⟩, h1 hx, rfl⟩

end SylowTools

end CFSG.ClassicalInvolution.GlaubermanAut
