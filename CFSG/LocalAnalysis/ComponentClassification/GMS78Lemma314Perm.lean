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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.ComponentClassification.GMS78

open Subgroup Pointwise

theorem smul_eq_of_isPGroup {X Ω : Type*} [Group X] [MulAction X Ω] [Finite Ω] {p : ℕ}
    [hp : Fact p.Prime] {P : Subgroup X} (hP : IsPGroup p P) {c : X}
    (hc : c ∈ normalizer (P : Set X)) {α : Ω} (hα : ∀ g ∈ P, g • α = α)
    (htrans : ∀ β γ : Ω, β ≠ α → γ ≠ α → ∃ k : ℤ, c ^ k • β = γ) (hdvd : p ∣ Nat.card Ω) :
    ∀ g ∈ P, ∀ β : Ω, g • β = β := by
  classical
  have h1 := hP.card_modEq_card_fixedPoints Ω
  have hfixα : α ∈ MulAction.fixedPoints P Ω := fun g => hα g g.2
  obtain ⟨β₀, hβ₀, hβ₀α⟩ : ∃ β₀ ∈ MulAction.fixedPoints P Ω, β₀ ≠ α := by
    by_contra hall
    push Not at hall
    have hset : MulAction.fixedPoints P Ω = {α} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨hfixα, hall⟩
    rw [hset, show Nat.card ({α} : Set Ω) = 1 from Nat.card_unique] at h1
    have h3 : Nat.card Ω % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h4 : 1 % p = 1 := Nat.mod_eq_of_lt hp.out.one_lt
    unfold Nat.ModEq at h1
    omega
  intro g hg β
  by_cases hβ : β = α
  · rw [hβ]
    exact hα g hg
  obtain ⟨k, rfl⟩ := htrans β₀ β hβ₀α hβ
  have hck : (c ^ k)⁻¹ ∈ normalizer (P : Set X) := inv_mem (zpow_mem hc k)
  have hg' : (c ^ k)⁻¹ * g * c ^ k ∈ P := by
    have := (mem_normalizer_iff.mp hck g).mp hg
    rwa [inv_inv] at this
  have h2 : ((c ^ k)⁻¹ * g * c ^ k) • β₀ = β₀ := hβ₀ ⟨_, hg'⟩
  calc g • c ^ k • β₀ = c ^ k • ((c ^ k)⁻¹ * g * c ^ k) • β₀ := by
        rw [← mul_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
    _ = c ^ k • β₀ := by rw [h2]

theorem twoTransitive_of {Ω : Type*} {X : Subgroup (Equiv.Perm Ω)}
    (htrans : ∀ β γ : Ω, ∃ x ∈ X, x β = γ) {α : Ω} {c : Equiv.Perm Ω} (hcX : c ∈ X)
    (hcα : c α = α) (hc : ∀ β γ : Ω, β ≠ α → γ ≠ α → ∃ k : ℤ, (c ^ k) β = γ) :
    ∀ a b a' b' : Ω, a ≠ b → a' ≠ b' → ∃ x ∈ X, x a = a' ∧ x b = b' := by
  intro a b a' b' hab hab'
  obtain ⟨x₁, hx₁, hx₁a⟩ := htrans α a
  obtain ⟨x₂, hx₂, hx₂a⟩ := htrans α a'
  have hb : x₁⁻¹ b ≠ α := fun h1 => hab (by rw [← hx₁a, ← h1]; exact x₁.apply_symm_apply b)
  have hb' : x₂⁻¹ b' ≠ α := fun h1 => hab' (by rw [← hx₂a, ← h1]; exact x₂.apply_symm_apply b')
  obtain ⟨k, hk⟩ := hc _ _ hb hb'
  refine ⟨x₂ * c ^ k * x₁⁻¹, mul_mem (mul_mem hx₂ (zpow_mem hcX k)) (inv_mem hx₁), ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    rw [← hx₁a, ← hx₂a]
    rw [show x₁⁻¹ (x₁ α) = α from x₁.symm_apply_apply α,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hcα k]
  · simp only [Equiv.Perm.mul_apply]
    rw [hk]
    exact x₂.apply_symm_apply b'

end CFSG.ComponentClassification.GMS78
