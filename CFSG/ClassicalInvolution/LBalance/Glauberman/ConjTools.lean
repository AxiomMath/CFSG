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

section Conj

variable {Ω : Type*} [Group Ω]

@[expose] def cj (g : Ω) (A : Subgroup Ω) : Subgroup Ω := A.comap (MulAut.conj g).toMonoidHom

@[simp] theorem mem_cj {g x : Ω} {A : Subgroup Ω} : x ∈ cj g A ↔ g * x * g⁻¹ ∈ A := Iff.rfl

theorem cj_le_cj {g : Ω} {A B : Subgroup Ω} (h : A ≤ B) : cj g A ≤ cj g B := fun _ hx => h hx

theorem cj_le_cj_iff {g : Ω} {A B : Subgroup Ω} : cj g A ≤ cj g B ↔ A ≤ B := by
  refine ⟨fun h x hx => ?_, cj_le_cj⟩
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  have := @h (g⁻¹ * x * g) (by rw [mem_cj, e]; exact hx)
  rwa [mem_cj, e] at this

theorem cj_inf {g : Ω} (A B : Subgroup Ω) : cj g (A ⊓ B) = cj g A ⊓ cj g B := rfl

theorem cj_cj {g h : Ω} (A : Subgroup Ω) : cj g (cj h A) = cj (h * g) A := by
  ext x
  simp only [mem_cj]
  rw [show h * (g * x * g⁻¹) * h⁻¹ = h * g * x * (h * g)⁻¹ by group]

theorem cj_one (A : Subgroup Ω) : cj 1 A = A := by
  ext x
  simp

theorem cj_of_mem_normalizer {g : Ω} {A : Subgroup Ω} (hg : g ∈ Subgroup.normalizer (A : Set Ω)) :
    cj g A = A := by
  ext x
  simp only [mem_cj]
  exact ((Subgroup.mem_normalizer_iff.1 hg) x).symm

theorem cj_normalizer {g : Ω} (A : Subgroup Ω) :
    cj g (Subgroup.normalizer (A : Set Ω)) = Subgroup.normalizer (cj g A : Set Ω) := by
  ext x
  simp only [mem_cj, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    simpa [mul_assoc] using this
  · intro h y
    have := h (g⁻¹ * y * g)
    simpa [mul_assoc] using this

theorem cj_centralizer {g : Ω} (A : Subgroup Ω) :
    cj g (Subgroup.centralizer (A : Set Ω)) = Subgroup.centralizer (cj g A : Set Ω) := by
  ext x
  simp only [mem_cj, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h y hy
    have h1 := h (g * y * g⁻¹) hy
    have h2 : g * (y * x) * g⁻¹ = g * (x * y) * g⁻¹ := by
      rw [show g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) by group,
        show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group, h1]
    simpa using h2
  · intro h y hy
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have h1 := h (g⁻¹ * y * g) (by rw [e]; exact hy)
    have h2 : g * (g⁻¹ * y * g * x) * g⁻¹ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    simpa [mul_assoc] using h2

theorem cj_eq_map (g : Ω) (A : Subgroup Ω) : cj g A = A.map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  simp only [mem_cj, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha

theorem card_cj (g : Ω) (A : Subgroup Ω) : Nat.card (cj g A) = Nat.card A := by
  rw [cj_eq_map]
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem isPGroup_cj {p : ℕ} {g : Ω} {A : Subgroup Ω} (hA : IsPGroup p A) : IsPGroup p (cj g A) :=
  hA.comap_of_injective _ (MulAut.conj g).injective

theorem relIndex_cj (g : Ω) (A B : Subgroup Ω) : (cj g A).relIndex (cj g B) = A.relIndex B := by
  have : cj g B = B.map (MulAut.conj g⁻¹).toMonoidHom := cj_eq_map g B
  rw [cj_eq_map, cj_eq_map]
  exact Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g⁻¹).injective

variable {p : ℕ} [Fact p.Prime] [Finite Ω]

theorem isSylowOf_cj_iff {A B : Subgroup Ω} (g : Ω) :
    IsSylowOf p (cj g A) (cj g B) ↔ IsSylowOf p A B := by
  rw [isSylowOf_iff, isSylowOf_iff, cj_le_cj_iff, relIndex_cj]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    have := isPGroup_cj (g := g⁻¹) h2
    rwa [cj_cj, mul_inv_cancel, cj_one] at this
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, isPGroup_cj h2, h3⟩

end Conj

end CFSG.ClassicalInvolution.GlaubermanAut
