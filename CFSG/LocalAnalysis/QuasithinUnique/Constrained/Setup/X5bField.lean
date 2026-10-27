module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

open Polynomial CFSG.LocalAnalysis.ComponentInitial FiniteField

namespace CFSG.QuasithinUnique.Setup.X5

variable {f : ℕ} {K : Type} [Field K]

theorem root_identities {R : Type*} [CommRing R] {x : R} (hquad : x ^ 2 - x + 1 = 0) :
    x = x ^ 2 + 1 ∧ x ^ 2 * x = x ^ 2 + x ^ 2 * x ^ 2 ∧ x ^ 2 * x ^ 2 * x = x ^ 2 * x ^ 2 + 1 ∧
      1 + x ^ 2 + x ^ 2 * x ^ 2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-1 : R) * hquad
  · linear_combination (-(x ^ 2)) * hquad
  · linear_combination (x ^ 3 - x - 1) * hquad
  · linear_combination (x ^ 2 + x + 1) * hquad

theorem exists_cubic_factor (h : UnitaryFieldData 2 f K) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hord : orderOf (2 : ZMod ℓ) = 6 * f)
    (hx6 : orderOf (((2 ^ f : ℕ) : ZMod ℓ)) = 6)
    (hquad : (((2 ^ f : ℕ) : ZMod ℓ)) ^ 2 - ((2 ^ f : ℕ) : ZMod ℓ) + 1 = 0) :
    ∃ τ : K, τ + h.bar τ ≠ 0 ∧
      ((X : K[X]) ^ 3 + C τ * X ^ 2 + C (h.bar τ) * X + 1) ∣ (X ^ ℓ - 1) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : CharP K 2 := h.charP
  have : Finite K := h.finite
  let E := FiniteField.Extension K 2 3
  have hEc : CharP E 2 := charP_of_injective_algebraMap (algebraMap K E).injective 2
  have hE2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hcardK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  have hcardE : Nat.card E = 2 ^ (6 * f) := by
    rw [natCard_extension, hcardK, ← pow_mul, ← pow_mul]
    congr 1; ring
  have h2pow : (2 : ZMod ℓ) ^ (6 * f) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hdvd : ℓ ∣ Nat.card Eˣ := by
    rw [Nat.card_units, hcardE, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow,
      Nat.cast_pow, Nat.cast_ofNat, h2pow, Nat.cast_one, sub_self]
  obtain ⟨θu, hθu⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  obtain ⟨θ, hθ⟩ : ∃ θ : E, θ = θu := ⟨_, rfl⟩
  have hθo : orderOf θ = ℓ := by rw [hθ, orderOf_units]; exact hθu
  have hθℓ : θ ^ ℓ = 1 := by rw [← hθo]; exact pow_orderOf_eq_one θ
  have hθpow : ∀ a b : ℕ, (a : ZMod ℓ) = (b : ZMod ℓ) → θ ^ a = θ ^ b := fun a b hab => by
    have := (pow_eq_pow_iff_modEq (x := θu) (n := a) (m := b)).mpr
      (by rw [hθu]; exact (ZMod.natCast_eq_natCast_iff a b ℓ).mp hab)
    rw [hθ, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, this]
  have hθpow' : ∀ a b : ℕ, θ ^ a = θ ^ b → (a : ZMod ℓ) = (b : ZMod ℓ) := fun a b hab => by
    have h1 : θu ^ a = θu ^ b := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hθ]
      exact hab
    exact (ZMod.natCast_eq_natCast_iff a b ℓ).mpr (by
      rw [← hθu]; exact (pow_eq_pow_iff_modEq (x := θu) (n := a) (m := b)).mp h1)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = 2 ^ f := ⟨_, rfl⟩
  rw [← hQ] at hx6 hquad hcardK
  obtain ⟨x, hx⟩ : ∃ x : ZMod ℓ, x = (Q : ZMod ℓ) := ⟨_, rfl⟩
  rw [← hx] at hx6 hquad
  have hx6' : x ^ 6 = 1 := by rw [← hx6]; exact pow_orderOf_eq_one x
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hx6'
    simp at hx6'
  have hxne : ∀ k : ℕ, 0 < k → k < 6 → x ^ k ≠ 1 := fun k hk hk6 =>
    pow_ne_one_of_lt_orderOf hk.ne' (by rw [hx6]; exact hk6)
  let φ := FiniteField.Extension.frob K 2 3
  have hφ : ∀ y : E, φ y = y ^ (Q ^ 2) := fun y => by
    rw [FiniteField.Extension.frob_apply, hcardK]
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : E, θ₁ = φ θ := ⟨_, rfl⟩
  obtain ⟨θ₂, hθ₂⟩ : ∃ θ₂ : E, θ₂ = φ θ₁ := ⟨_, rfl⟩
  have hθ₁' : θ₁ = θ ^ (Q ^ 2) := by rw [hθ₁, hφ]
  have hθ₂' : θ₂ = θ ^ (Q ^ 2 * Q ^ 2) := by
    rw [hθ₂, hφ, hθ₁', ← pow_mul]
  have hφθ₂ : φ θ₂ = θ := by
    rw [hφ, hθ₂', ← pow_mul]
    conv_rhs => rw [← pow_one θ]
    apply hθpow
    push_cast
    rw [← hx]
    calc (x ^ 2 * x ^ 2 * x ^ 2 : ZMod ℓ) = x ^ 6 := by ring
      _ = 1 := hx6'
  have hfix : ∀ y : E, φ y = y → ∃ z : K, algebraMap K E z = y := by
    intro y hy
    have hmem : y ∈ (⊥ : IntermediateField K E) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro σ
      obtain ⟨i, -, rfl⟩ := FiniteField.Extension.exists_frob_pow_eq K 2 3 σ
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, AlgEquiv.mul_apply, hy, ih]
    exact IntermediateField.mem_bot.mp hmem
  have hθ₁φ : φ θ = θ₁ := hθ₁.symm
  have hθ₂φ : φ θ₁ = θ₂ := hθ₂.symm
  obtain ⟨τ, hτ⟩ := hfix (θ + θ₁ + θ₂)
    (by rw [map_add, map_add, hθ₁φ, hθ₂φ, hφθ₂]; ring)
  obtain ⟨s₂, hs₂⟩ := hfix (θ * θ₁ + θ₁ * θ₂ + θ₂ * θ)
    (by rw [map_add, map_add, map_mul, map_mul, map_mul, hθ₁φ, hθ₂φ, hφθ₂]; ring)
  obtain ⟨s₃, hs₃⟩ := hfix (θ * θ₁ * θ₂)
    (by rw [map_mul, map_mul, hθ₁φ, hθ₂φ, hφθ₂]; ring)
  have hι : Function.Injective (algebraMap K E) := (algebraMap K E).injective
  obtain ⟨hr1, hr2, hr3, hr4⟩ := root_identities hquad
  have e4 : θ * θ₁ * θ₂ = 1 := by
    calc θ * θ₁ * θ₂ = θ ^ (1 + Q ^ 2 + Q ^ 2 * Q ^ 2) := by
          rw [hθ₁', hθ₂', pow_add, pow_add, pow_one]
      _ = θ ^ 0 := hθpow _ _ (by push_cast; rw [← hx]; exact hr4)
      _ = 1 := pow_zero θ
  have hs₃1 : s₃ = 1 := by
    apply hι
    rw [hs₃, e4, map_one]
  have hq1 : θ ^ Q = θ * θ₁ := by
    rw [hθ₁', ← pow_succ']
    exact hθpow _ _ (by push_cast; rw [← hx]; exact hr1)
  have hq2 : θ₁ ^ Q = θ₁ * θ₂ := by
    rw [hθ₁', hθ₂', ← pow_mul, ← pow_add]
    exact hθpow _ _ (by push_cast; rw [← hx]; exact hr2)
  have hq3 : θ₂ ^ Q = θ₂ * θ := by
    rw [hθ₂', ← pow_mul, ← pow_succ]
    exact hθpow _ _ (by push_cast; rw [← hx]; exact hr3)
  have hs₂bar : s₂ = h.bar τ := by
    apply hι
    rw [hs₂, UnitaryFieldData.bar_apply, map_pow, hτ, ← hQ,
      show Q = 2 ^ f from hQ, add_pow_char_pow, add_pow_char_pow, ← hQ, hq1, hq2, hq3]

  have hθ1 : θ ≠ 1 := by
    intro h0
    have h1 : orderOf θ = 1 := by rw [h0]; exact orderOf_one
    rw [hθo] at h1
    exact hℓ.one_lt.ne' h1
  have hx2 : x ^ 2 ≠ 1 := hxne 2 (by norm_num) (by norm_num)
  have hx4 : x ^ 2 * x ^ 2 ≠ 1 := by
    have := hxne 4 (by norm_num) (by norm_num)
    rwa [show x ^ 4 = x ^ 2 * x ^ 2 by rw [← pow_add]] at this
  have hθ₁1 : θ₁ ≠ 1 := by
    intro h0
    have h1 := hθpow' (Q ^ 2) 0 (by rw [← hθ₁', h0, pow_zero])
    push_cast at h1
    rw [← hx] at h1
    exact hx0 (pow_eq_zero_iff (by norm_num) |>.mp h1)
  have hθ₂1 : θ₂ ≠ 1 := by
    intro h0
    have h1 := hθpow' (Q ^ 2 * Q ^ 2) 0 (by rw [← hθ₂', h0, pow_zero])
    push_cast at h1
    rw [← hx] at h1
    have : x ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2 <;> exact h2
    exact hx0 (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hθθ₁ : θ ≠ θ₁ := by
    intro h0
    have h1 := hθpow' 1 (Q ^ 2) (by rw [pow_one, ← hθ₁', h0])
    push_cast at h1
    rw [← hx] at h1
    exact hx2 h1.symm
  have hθθ₂ : θ ≠ θ₂ := by
    intro h0
    have h1 := hθpow' 1 (Q ^ 2 * Q ^ 2) (by rw [pow_one, ← hθ₂', h0])
    push_cast at h1
    rw [← hx] at h1
    exact hx4 h1.symm
  have hθ₁θ₂ : θ₁ ≠ θ₂ := by
    intro h0
    have h1 := hθpow' (Q ^ 2) (Q ^ 2 * Q ^ 2) (by rw [← hθ₁', ← hθ₂', h0])
    push_cast at h1
    rw [← hx] at h1
    have h2 : x ^ 2 * (1 - x ^ 2) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hx0 (pow_eq_zero_iff (by norm_num) |>.mp h3)
    · exact hx2 (sub_eq_zero.mp h3).symm
  have hne : τ + h.bar τ ≠ 0 := by
    intro h0
    have key : (1 - θ) * (1 - θ₁) * (1 - θ₂) = algebraMap K E (τ + h.bar τ) := by
      rw [map_add, hτ, ← hs₂bar, hs₂]
      linear_combination (-1 : E) * e4 + (-(θ + θ₁ + θ₂)) * hE2
    rw [h0, map_zero] at key
    rcases mul_eq_zero.mp key with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact hθ1 (sub_eq_zero.mp h2).symm
      · exact hθ₁1 (sub_eq_zero.mp h2).symm
    · exact hθ₂1 (sub_eq_zero.mp h1).symm
  refine ⟨τ, hne, ?_⟩
  have h2P : (2 : E[X]) = 0 := by
    have : (2 : E[X]) = C 2 := (map_ofNat C 2).symm
    rw [this, hE2, C_0]
  have hmapP : (((X : K[X]) ^ 3 + C τ * X ^ 2 + C (h.bar τ) * X + 1).map (algebraMap K E)) =
      (X - C θ) * (X - C θ₁) * (X - C θ₂) := by
    have hRHS : (X - C θ) * (X - C θ₁) * (X - C θ₂) = X ^ 3 - C (θ + θ₁ + θ₂) * X ^ 2 +
        C (θ * θ₁ + θ₁ * θ₂ + θ₂ * θ) * X - C (θ * θ₁ * θ₂) := by
      simp only [C_add, C_mul]; ring
    rw [hRHS, e4, C_1]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_one]
    rw [hτ, ← hs₂bar, hs₂]
    linear_combination (C (θ + θ₁ + θ₂) * X ^ 2 + 1) * h2P
  have hθ₁ℓ : θ₁ ^ ℓ = 1 := by rw [hθ₁', ← pow_mul, mul_comm, pow_mul, hθℓ, one_pow]
  have hθ₂ℓ : θ₂ ^ ℓ = 1 := by rw [hθ₂', ← pow_mul, mul_comm, pow_mul, hθℓ, one_pow]
  have hroot : ∀ y : E, y ^ ℓ = 1 → ((X : E[X]) ^ ℓ - 1).IsRoot y := fun y hy => by
    simp [hy]
  obtain ⟨F₁, hF₁⟩ := dvd_iff_isRoot.mpr (hroot θ hθℓ)
  have hF₁root : F₁.IsRoot θ₁ := by
    have := hroot θ₁ hθ₁ℓ
    rw [hF₁, IsRoot.def, eval_mul] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by simpa [sub_eq_zero] using h0) (Ne.symm hθθ₁)
    · exact h0
  obtain ⟨F₂, hF₂⟩ := dvd_iff_isRoot.mpr hF₁root
  have hF₂root : F₂.IsRoot θ₂ := by
    have := hroot θ₂ hθ₂ℓ
    rw [hF₁, hF₂, IsRoot.def, eval_mul, eval_mul] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (by simpa [sub_eq_zero] using h0) (Ne.symm hθθ₂)
    · rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd (by simpa [sub_eq_zero] using h1) (Ne.symm hθ₁θ₂)
      · exact h1
  obtain ⟨F₃, hF₃⟩ := dvd_iff_isRoot.mpr hF₂root
  have hmonic : ((X : K[X]) ^ 3 + C τ * X ^ 2 + C (h.bar τ) * X + 1).Monic := by monicity!
  refine (Polynomial.map_dvd_map (algebraMap K E) hι hmonic).mp ⟨F₃, ?_⟩
  rw [hmapP]
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  rw [hF₁, hF₂, hF₃]
  ring

end CFSG.QuasithinUnique.Setup.X5
