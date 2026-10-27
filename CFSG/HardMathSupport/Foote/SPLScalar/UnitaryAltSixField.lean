
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

section Field

variable {K : Type*} [Field K] [CharP K 3] (σ : K ≃+* K)

@[expose] def tAct (k : K) (z : K × K) : K × K := (z.1 * k * (σ k)⁻¹ ^ 2, z.2 * (σ k)⁻¹ * k⁻¹)

@[expose] def rConj (s : K) (z : K × K) : K × K := (z.1, z.2 + z.1 * σ s - s * σ z.1)

@[expose] def wAct (k s : K) (z : K × K) : K × K := rConj σ s (tAct σ k z)

theorem three_eq_zero : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3

theorem two_eq_neg_one : (2 : K) = -1 := by
  have := three_eq_zero (K := K)
  linear_combination this

omit [CharP K 3] in
theorem cube_eq_zero {x : K} (h : x ^ 3 = 0) : x = 0 := pow_eq_zero_iff (by norm_num) |>.mp h

theorem eq_one_of_pow_three {x : K} (h : x ^ 3 = 1) : x = 1 := by
  have h3 := three_eq_zero (K := K)
  have : (x - 1) ^ 3 = 0 := by
    linear_combination h + (-x ^ 2 + x) * h3
  exact sub_eq_zero.mp (cube_eq_zero this)

theorem kappa_injective (hσ : ∀ x, σ (σ x) = x) {k k' : K} (hk : k ≠ 0) (hk' : k' ≠ 0)
    (h : k * (σ k)⁻¹ ^ 2 = k' * (σ k')⁻¹ ^ 2) : k = k' := by
  have hσk : σ k ≠ 0 := (map_ne_zero σ).mpr hk
  have hσk' : σ k' ≠ 0 := (map_ne_zero σ).mpr hk'
  have h1 : k * (σ k') ^ 2 = k' * (σ k) ^ 2 := by
    field_simp at h
    linear_combination h
  set u := k / k' with hu
  have hu0 : u ≠ 0 := div_ne_zero hk hk'
  have hσu : σ u = σ k / σ k' := by rw [hu, map_div₀]
  have hu1 : u = (σ u) ^ 2 := by
    rw [hσu, hu]
    field_simp
    linear_combination h1
  have hu2 : σ u = u ^ 2 := by
    have := congrArg σ hu1
    rwa [map_pow, hσ] at this
  have hu3 : u ^ 3 = 1 := by
    have h4 : u = u ^ 4 := by
      calc u = (σ u) ^ 2 := hu1
        _ = (u ^ 2) ^ 2 := by rw [hu2]
        _ = u ^ 4 := by ring
    have : u * (u ^ 3 - 1) = 0 := by linear_combination -h4
    have := (mul_eq_zero.mp this).resolve_left hu0
    exact sub_eq_zero.mp this
  have : u = 1 := eq_one_of_pow_three hu3
  rw [hu, div_eq_one_iff_eq hk'] at this
  exact this

omit [CharP K 3] in
theorem kappa_facts (hσ : ∀ x, σ (σ x) = x) {ι : K} (hι : ι ^ 2 = -1) (hιF : σ ι = ι)
    {k : K} (hk : k ≠ 0) {s a₁ b₁ : K} (ha₁ : a₁ ≠ 0)
    (hW : wAct σ k s (wAct σ k s (a₁, b₁)) = (-a₁, σ b₁)) :
    (k * (σ k) ⁻¹ ^ 2) ^ 2 = -1 ∧ σ (k * (σ k) ⁻¹ ^ 2) = k * (σ k) ⁻¹ ^ 2 ∧ k * σ k = -1 := by
  have hσk : σ k ≠ 0 := (map_ne_zero σ).mpr hk
  have h1 := congrArg Prod.fst hW
  simp only [wAct, rConj, tAct] at h1
  have hκ2 : (k * (σ k)⁻¹ ^ 2) ^ 2 = -1 := by
    have : a₁ * ((k * (σ k)⁻¹ ^ 2) ^ 2 + 1) = 0 := by
      linear_combination h1
    have := (mul_eq_zero.mp this).resolve_left ha₁
    linear_combination this
  have hκF : σ (k * (σ k)⁻¹ ^ 2) = k * (σ k)⁻¹ ^ 2 := by
    set κ := k * (σ k)⁻¹ ^ 2
    have : (κ - ι) * (κ + ι) = 0 := by linear_combination hκ2 - hι
    rcases mul_eq_zero.mp this with h | h
    · have : κ = ι := sub_eq_zero.mp h
      rw [this, hιF]
    · have : κ = -ι := eq_neg_of_add_eq_zero_left h
      rw [this, map_neg, hιF]
  refine ⟨hκ2, hκF, ?_⟩
  have hσκ : σ (k * (σ k)⁻¹ ^ 2) = σ k * (k⁻¹) ^ 2 := by
    rw [map_mul, map_pow, map_inv₀, hσ]
  have h2 : (k * (σ k)⁻¹ ^ 2) * (σ k * k⁻¹ ^ 2) = (k * σ k)⁻¹ := by
    field_simp
  rw [← hσκ, hκF, ← sq, hκ2] at h2
  have : k * σ k ≠ 0 := mul_ne_zero hk hσk
  field_simp at h2
  linear_combination -h2

theorem exists_kappa_eq (hσ : ∀ x, σ (σ x) = x) [Finite K] {ζ : K} (hζ : ζ ≠ 0) :
    ∃ k : K, k ≠ 0 ∧ k * (σ k)⁻¹ ^ 2 = ζ := by
  let g : Kˣ → Kˣ := fun u => Units.mk0 ((u : K) * (σ (u : K))⁻¹ ^ 2) (by
    have hu : (u : K) ≠ 0 := u.ne_zero
    have : σ (u : K) ≠ 0 := (map_ne_zero σ).mpr hu
    positivity)
  have hg : Function.Injective g := by
    intro u v huv
    have h := congrArg (fun x : Kˣ => (x : K)) huv
    exact Units.ext (kappa_injective σ hσ u.ne_zero v.ne_zero h)
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hg) (Units.mk0 ζ hζ)
  exact ⟨u, u.ne_zero, by simpa [g] using congrArg (fun x : Kˣ => (x : K)) hu⟩

omit [CharP K 3] in
theorem kappa_mul_sigma (hσ : ∀ x, σ (σ x) = x) {k : K} (hk : k ≠ 0) :
    (k * (σ k)⁻¹ ^ 2) * σ (k * (σ k)⁻¹ ^ 2) = (k * σ k)⁻¹ := by
  have hσk : σ k ≠ 0 := (map_ne_zero σ).mpr hk
  rw [map_mul, map_pow, map_inv₀, hσ]
  field_simp

theorem singer_field_core [Finite K] (hσ : ∀ x, σ (σ x) = x) {ι : K} (hι : ι ^ 2 = -1)
    (hιF : σ ι = ι) {k : K} (hk : k ≠ 0) {s a₁ b₁ : K} (ha₁ : a₁ ≠ 0)
    (hb₁ : b₁ + σ b₁ + a₁ * σ a₁ = 0)
    (hW : wAct σ k s (wAct σ k s (a₁, b₁)) = (-a₁, σ b₁)) :
    (k * (σ k)⁻¹ ^ 2) ^ 2 = -1 ∧ ∃ k₈ : K, k₈ ≠ 0 ∧ ∃ s' : K,
      wAct σ k₈ s' (a₁, b₁) =
        (a₁ - (wAct σ k s (a₁, b₁)).1,
          b₁ + σ (wAct σ k s (a₁, b₁)).2 + a₁ * σ (wAct σ k s (a₁, b₁)).1) ∧
      wAct σ k₈ s' (wAct σ k s (a₁, b₁)) =
        (a₁ + (wAct σ k s (a₁, b₁)).1,
          b₁ + (wAct σ k s (a₁, b₁)).2 - a₁ * σ (wAct σ k s (a₁, b₁)).1) := by
  obtain ⟨hκ2, hκF, hN⟩ := kappa_facts σ hσ hι hιF hk ha₁ hW
  refine ⟨hκ2, ?_⟩
  have hσk : σ k ≠ 0 := (map_ne_zero σ).mpr hk
  have h3 := three_eq_zero (K := K)
  set κ := k * (σ k)⁻¹ ^ 2 with hκdef
  have hκ0 : κ ≠ 0 := by
    intro h
    rw [h] at hκ2
    norm_num at hκ2
  set Φ := a₁ * σ s - s * σ a₁ with hΦ
  have hσΦ : σ Φ = -Φ := by
    rw [hΦ, map_sub, map_mul, map_mul, hσ, hσ]
    ring
  have hinvN : (σ k)⁻¹ * k⁻¹ = -1 := by
    have : (σ k)⁻¹ * k⁻¹ = (k * σ k)⁻¹ := by field_simp
    rw [this, hN]
    norm_num
  have hz1 : (wAct σ k s (a₁, b₁)).1 = a₁ * κ := by
    simp only [wAct, rConj, tAct]
    rw [hκdef]
    ring
  have hz2 : (wAct σ k s (a₁, b₁)).2 = -b₁ + κ * Φ := by
    have e : a₁ * k * (σ k)⁻¹ ^ 2 = a₁ * κ := by rw [hκdef]; ring
    simp only [wAct, rConj, tAct]
    rw [mul_assoc b₁, hinvN, e, map_mul, hκF, hΦ]
    ring
  set n := a₁ * σ a₁ with hn
  have hz2eq : wAct σ k s (a₁, b₁) = (a₁ * κ, -b₁ + κ * Φ) := Prod.ext hz1 hz2
  have hR2 : σ b₁ = b₁ - κ * Φ - Φ := by
    have h2 := congrArg Prod.snd hW
    rw [hz2eq] at h2
    simp only [wAct, rConj, tAct] at h2
    have e : a₁ * κ * k * (σ k)⁻¹ ^ 2 = -a₁ := by
      have : a₁ * κ * k * (σ k)⁻¹ ^ 2 = a₁ * κ ^ 2 := by rw [hκdef]; ring
      rw [this, hκ2]; ring
    rw [mul_assoc (-b₁ + κ * Φ), hinvN, e, map_neg, hΦ] at h2
    linear_combination -h2
  have hbσ : σ b₁ = -b₁ - n := by linear_combination hb₁
  have hrel : (1 + κ) * Φ = 2 * b₁ + n := by linear_combination hR2 - hbσ
  have h1κ : 1 + κ ≠ 0 := by
    intro h
    have : κ = -1 := by linear_combination h
    rw [this] at hκ2
    norm_num at hκ2
    have : (2 : K) = 0 := by linear_combination hκ2
    have h2 : (2 : K) = -1 := two_eq_neg_one
    rw [h2] at this
    have h1 : (1 : K) = 0 := by linear_combination -this
    exact one_ne_zero h1
  set ζ := 1 - κ with hζdef
  have hσζ : σ ζ = ζ := by rw [hζdef, map_sub, map_one, hκF]
  have hζ2 : ζ ^ 2 = κ := by
    rw [hζdef]
    linear_combination hκ2 + (-κ) * h3
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h] at hζ2
    exact hκ0 (by simpa using hζ2.symm)
  obtain ⟨k₈, hk₈, hκ₈⟩ := exists_kappa_eq σ hσ hζ0
  have hσk₈ : σ k₈ ≠ 0 := (map_ne_zero σ).mpr hk₈
  have hN₈ : (σ k₈)⁻¹ * k₈⁻¹ = ζ ^ 2 := by
    have h := kappa_mul_sigma σ hσ hk₈
    rw [hκ₈, hσζ] at h
    have : (σ k₈)⁻¹ * k₈⁻¹ = (k₈ * σ k₈)⁻¹ := by field_simp
    rw [this, ← h]
    ring
  have e8 : ∀ x : K, x * k₈ * (σ k₈)⁻¹ ^ 2 = x * ζ := fun x => by
    rw [← hκ₈]; ring
  have h2ne : (2 : K) ≠ 0 := by
    rw [two_eq_neg_one]
    exact neg_ne_zero.mpr one_ne_zero
  have hσb₂ : σ (-b₁ + κ * Φ) = b₁ + n - κ * Φ := by
    rw [map_add, map_neg, map_mul, hκF, hσΦ, hbσ]
    ring
  have hσa₂ : σ (a₁ * κ) = σ a₁ * κ := by rw [map_mul, hκF]
  have hσn : σ n = n := by rw [hn, map_mul, hσ]; ring
  set β₁ := b₁ + σ (-b₁ + κ * Φ) + a₁ * σ (a₁ * κ) with hβ₁
  have hβ₁' : β₁ = 2 * b₁ + n + κ * n - κ * Φ := by
    rw [hβ₁, hσb₂, hσa₂, hn]
    ring
  set y := (β₁ - κ * b₁) / ζ with hy
  have hζy : ζ * y = β₁ - κ * b₁ := by rw [hy]; field_simp
  have hσβ : σ β₁ = -(2 * b₁) - n + κ * n + κ * Φ := by
    rw [hβ₁']
    simp only [map_add, map_sub, map_mul, map_ofNat, hκF, hσΦ, hσn, hbσ]
    ring
  have hσy : σ y = -y := by
    have h1 : ζ * σ y = -(ζ * y) := by
      have : σ (ζ * y) = σ (β₁ - κ * b₁) := by rw [hζy]
      rw [map_mul, hσζ] at this
      rw [this, hζy, map_sub, map_mul, hκF, hσβ, hbσ, hβ₁']
      linear_combination (κ * n) * h3
    exact mul_left_cancel₀ hζ0 (h1.trans (by ring : -(ζ * y) = ζ * (-y)))
  set s' := σ (y / (2 * a₁)) with hs'
  have hΦ' : a₁ * σ s' - s' * σ a₁ = y := by
    have h1 : σ s' = y / (2 * a₁) := by rw [hs', hσ]
    have h2 : s' * σ a₁ = σ (y / 2) := by
      rw [hs', ← map_mul]
      congr 1
      field_simp
    have e1 : a₁ * (y / (2 * a₁)) = y / 2 := by field_simp
    have h3' : σ (y / 2) = -y / 2 := by rw [map_div₀, hσy, map_ofNat]
    rw [h1, e1, h2, h3']
    field_simp
    ring
  have hX : (1 + κ) * b₁ + (2 * κ - 1) * n - κ * Φ = 0 := by
    have : (1 + κ) * ((1 + κ) * b₁ + (2 * κ - 1) * n - κ * Φ) = 0 := by
      linear_combination (-κ) * hrel + (b₁ + 2 * n) * hκ2 - n * h3
    exact (mul_eq_zero.mp this).resolve_left h1κ
  refine ⟨k₈, hk₈, s', ?_, ?_⟩
  · rw [hz1, hz2]
    refine Prod.ext ?_ ?_
    · simp only [wAct, rConj, tAct]
      rw [e8, hζdef]
      ring
    · simp only [wAct, rConj, tAct]
      rw [mul_assoc b₁, hN₈, e8, map_mul, hσζ]
      linear_combination b₁ * hζ2 + ζ * hΦ' + hζy + hβ₁
  · rw [hz2eq]
    refine Prod.ext ?_ ?_
    · simp only [wAct, rConj, tAct]
      rw [e8, hζdef]
      linear_combination (-a₁) * hκ2
    · simp only [wAct, rConj, tAct]
      rw [mul_assoc (-b₁ + κ * Φ), hN₈, e8, map_mul, map_mul, hκF, hσζ]
      linear_combination (-b₁ + κ * Φ) * hζ2 + (κ * ζ) * hΦ' + κ * hζy + κ * hβ₁' + hX +
        (n - b₁) * hκ2

end Field

end CFSG.HardMathSupport.Foote.SPLScalar

