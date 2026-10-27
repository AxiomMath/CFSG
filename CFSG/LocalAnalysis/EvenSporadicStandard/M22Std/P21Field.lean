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

namespace CFSG.EvenSporadicStandard.M22Std.P21Field

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev Inv (f : V →ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) : Prop :=
  ∀ w ∈ W, f w ∈ W

omit [Module (ZMod 2) V] in
theorem odd_cast_zmod_two {ℓ : ℕ} (hℓ : Odd ℓ) : ((ℓ : ℕ) : ZMod 2) = 1 := by
  obtain ⟨k, rfl⟩ := hℓ
  rw [Nat.cast_add, Nat.cast_mul, show ((2 : ℕ) : ZMod 2) = 0 from by decide, zero_mul, zero_add,
    Nat.cast_one]

theorem ker_inf_range_eq_bot (f : V →ₗ[ZMod 2] V) {ℓ : ℕ} (hℓ : Odd ℓ) (hf : f ^ ℓ = 1) :
    LinearMap.ker (f - 1) ⊓ LinearMap.range (f - 1) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
  have hker : f v = v := by
    have := LinearMap.mem_ker.1 h1
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    exact this
  have hpow : ∀ i : ℕ, (f ^ i) v = v := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', Module.End.mul_apply, ih, hker]
  have hTv : (∑ i ∈ Finset.range ℓ, f ^ i) v = v := by
    rw [LinearMap.sum_apply]
    simp only [hpow, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), odd_cast_zmod_two hℓ, one_smul]
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 h2
  have hT : (∑ i ∈ Finset.range ℓ, f ^ i) * (f - 1) = 0 := by
    rw [geom_sum_mul, hf, sub_self]
  have h3 : (∑ i ∈ Finset.range ℓ, f ^ i) ((f - 1) w) = 0 := by
    have := congrArg (fun T => T w) hT
    simpa using this
  rw [← hTv, h3]
  exact Submodule.zero_mem _

theorem inv_range (f : V →ₗ[ZMod 2] V) : Inv f (LinearMap.range (f - 1)) := by
  intro w hw
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hw
  refine LinearMap.mem_range.2 ⟨f u, ?_⟩
  simp [LinearMap.sub_apply]


variable [Finite V]

theorem exists_minimal_invariant (f : V →ₗ[ZMod 2] V) {ℓ : ℕ} (hℓ : Odd ℓ) (hf : f ^ ℓ = 1)
    (hne : f ≠ 1) :
    ∃ S : Submodule (ZMod 2) V, S ≠ ⊥ ∧ S ≤ LinearMap.range (f - 1) ∧ Inv f S ∧
      (∀ W : Submodule (ZMod 2) V, W ≤ S → Inv f W → W = ⊥ ∨ W = S) ∧ ∃ s ∈ S, f s ≠ s := by
  classical
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let 𝒮 : Set (Submodule (ZMod 2) V) := {S | S ≠ ⊥ ∧ S ≤ LinearMap.range (f - 1) ∧ Inv f S}
  have h𝒮 : LinearMap.range (f - 1) ∈ 𝒮 := by
    refine ⟨?_, le_rfl, inv_range f⟩
    intro h
    apply hne
    have h0 : f - 1 = 0 := LinearMap.range_eq_bot.1 h
    exact sub_eq_zero.1 h0
  have hex : ∃ n, ∃ S ∈ 𝒮, Module.finrank (ZMod 2) S = n := ⟨_, _, h𝒮, rfl⟩
  obtain ⟨S, hS𝒮, hSn⟩ := Nat.find_spec hex
  have hmin : ∀ S' ∈ 𝒮, Module.finrank (ZMod 2) S ≤ Module.finrank (ZMod 2) S' := by
    intro S' hS'
    rw [hSn]
    exact Nat.find_min' hex ⟨S', hS', rfl⟩
  obtain ⟨hSne, hSr, hSinv⟩ := hS𝒮
  refine ⟨S, hSne, hSr, hSinv, ?_, ?_⟩
  · intro W hWS hWinv
    by_cases hW : W = ⊥
    · exact Or.inl hW
    · right
      have hW𝒮 : W ∈ 𝒮 := ⟨hW, hWS.trans hSr, hWinv⟩
      exact Submodule.eq_of_le_of_finrank_le hWS (hmin W hW𝒮)
  · by_contra hall
    push Not at hall
    apply hSne
    have hle : S ≤ LinearMap.ker (f - 1) := fun s hs => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hall s hs, sub_self]
    have := ker_inf_range_eq_bot f hℓ hf
    rw [eq_bot_iff, ← this]
    exact le_inf hle hSr

end CFSG.EvenSporadicStandard.M22Std.P21Field
