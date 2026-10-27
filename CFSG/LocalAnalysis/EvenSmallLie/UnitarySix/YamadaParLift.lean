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

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Subgroup
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

@[expose] def IsTwoElt (g : Γ) : Prop := ∃ n : ℕ, g ^ 2 ^ n = 1

theorem IsTwoElt.pow_eq_one {g : Γ} {n : ℕ} (hn : g ^ 2 ^ n = 1) {m : ℕ} (hm : n ≤ m) :
    g ^ 2 ^ m = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, pow_mul, hn, one_pow]

theorem isTwoElt_one : IsTwoElt (1 : Γ) := ⟨0, by simp⟩

theorem isTwoElt_of_sq {g : Γ} (h : g * g = 1) : IsTwoElt g := ⟨1, by rw [pow_one, sq, h]⟩

theorem IsTwoElt.conj {g : Γ} (hg : IsTwoElt g) (x : Γ) : IsTwoElt (x * g * x⁻¹) := by
  obtain ⟨n, hn⟩ := hg
  exact ⟨n, by rw [conj_pow, hn, mul_one, mul_inv_cancel]⟩

theorem IsTwoElt.mul_of_commute {g h : Γ} (hg : IsTwoElt g) (hh : IsTwoElt h) (hc : Commute g h) :
    IsTwoElt (g * h) := by
  obtain ⟨n, hn⟩ := hg
  obtain ⟨m, hm⟩ := hh
  refine ⟨max n m, ?_⟩
  rw [hc.mul_pow, IsTwoElt.pow_eq_one hn (le_max_left n m),
    IsTwoElt.pow_eq_one hm (le_max_right n m), one_mul]

section OddCentral

variable {Z : Subgroup Γ} (hZc : Z ≤ center Γ) (hZo : Odd (Nat.card Z))
include hZc hZo

omit hZc in
theorem eq_of_pow_two_pow {z w : Γ} (hz : z ∈ Z) (hw : w ∈ Z) (n : ℕ)
    (h : z ^ 2 ^ n = w ^ 2 ^ n) : z = w := by
  have hcop : (Nat.card Z).Coprime (2 ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hZo)
  have := (powCoprime hcop).injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩)
    (Subtype.ext (by simpa [powCoprime_apply] using h))
  simpa using congrArg Subtype.val this

omit hZc in
theorem exists_pow_two_pow {z : Γ} (hz : z ∈ Z) (n : ℕ) : ∃ w ∈ Z, w ^ 2 ^ n = z := by
  have hcop : (Nat.card Z).Coprime (2 ^ n) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hZo)
  obtain ⟨w, hw⟩ := (powCoprime hcop).surjective ⟨z, hz⟩
  refine ⟨w, w.2, ?_⟩
  have := congrArg Subtype.val hw
  simpa [powCoprime_apply] using this

theorem eq_of_isTwoElt {a b : Γ} (ha : IsTwoElt a) (hb : IsTwoElt b) (hab : a⁻¹ * b ∈ Z) :
    a = b := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  set w := a⁻¹ * b with hw
  have hb' : b = a * w := by rw [hw, mul_inv_cancel_left]
  have hcomm : Commute a w := (Subgroup.mem_center_iff.mp (hZc hab) a).symm.symm
  have h1 : w ^ 2 ^ max n m = 1 ^ 2 ^ max n m := by
    have := IsTwoElt.pow_eq_one hm (le_max_right n m)
    rw [hb', hcomm.mul_pow, IsTwoElt.pow_eq_one hn (le_max_left n m), one_mul] at this
    rw [this, one_pow]
  have := eq_of_pow_two_pow hZo hab Z.one_mem _ h1
  rw [hb', this, mul_one]

theorem exists_isTwoElt_mul {γ : Γ} {n : ℕ} (hγ : γ ^ 2 ^ n ∈ Z) :
    ∃ w ∈ Z, (γ * w) ^ 2 ^ n = 1 := by
  obtain ⟨w, hwZ, hw⟩ := exists_pow_two_pow hZo (Z.inv_mem hγ) n
  refine ⟨w, hwZ, ?_⟩
  have hcomm : Commute γ w := (Subgroup.mem_center_iff.mp (hZc hwZ) γ).symm.symm
  rw [hcomm.mul_pow, hw, mul_inv_cancel]

theorem commute_of_isTwoElt {a b : Γ} (ha : IsTwoElt a) (hb : IsTwoElt b) (hab : ⁅a, b⁆ ∈ Z) :
    Commute a b := by
  have _ := ha
  have hc := hb.conj a
  have hmem : b⁻¹ * (a * b * a⁻¹) ∈ Z := by
    have h1 : b⁻¹ * (a * b * a⁻¹) = b⁻¹ * (⁅a, b⁆ * b) := by
      rw [commutatorElement_def]; group
    rw [h1]
    have hcz := Subgroup.mem_center_iff.mp (hZc hab) b
    rw [← hcz, inv_mul_cancel_left]
    exact hab
  have := eq_of_isTwoElt hZc hZo hb hc hmem
  rw [Commute, SemiconjBy]
  calc a * b = (a * b * a⁻¹) * a := by group
    _ = b * a := by rw [← this]

theorem commutatorElement_eq_of_isTwoElt {a b c : Γ} (ha : IsTwoElt a) (hb : IsTwoElt b)
    (hc : IsTwoElt c) (hcb : Commute c b) (habc : ⁅a, b⁆⁻¹ * c ∈ Z) : ⁅a, b⁆ = c := by
  have _ := ha
  have hu := hb.conj a
  have hv := hc.mul_of_commute hb hcb
  have hmem : (a * b * a⁻¹)⁻¹ * (c * b) ∈ Z := by
    have h1 : (a * b * a⁻¹)⁻¹ * (c * b) = b⁻¹ * ((⁅a, b⁆⁻¹ * c) * b) := by
      rw [commutatorElement_def]; group
    rw [h1]
    have hz := Subgroup.mem_center_iff.mp (hZc habc) b
    rw [← hz, inv_mul_cancel_left]
    exact habc
  have := eq_of_isTwoElt hZc hZo hu hv hmem
  rw [commutatorElement_def, this, mul_inv_cancel_right]

end OddCentral

section FixedPoints

theorem inv_of_fixedPoints {N : Subgroup Γ} [Finite N] (τ : Γ →* Γ) (hτ : ∀ g, τ (τ g) = g)
    (hN : ∀ n ∈ N, τ n ∈ N) (hfix : ∀ n ∈ N, τ n = n → n = 1) : ∀ n ∈ N, τ n = n⁻¹ := by
  let κ : N → N := fun m => ⟨m⁻¹ * τ m, N.mul_mem (N.inv_mem m.2) (hN m m.2)⟩
  have hκ : Function.Injective κ := by
    rintro ⟨m, hm⟩ ⟨m', hm'⟩ h
    have h' : m⁻¹ * τ m = m'⁻¹ * τ m' := congrArg Subtype.val h
    have hfx : τ (m' * m⁻¹) = m' * m⁻¹ := by
      rw [map_mul, map_inv]
      calc τ m' * (τ m)⁻¹ = m' * (m'⁻¹ * τ m') * (m⁻¹ * τ m)⁻¹ * m⁻¹ := by group
        _ = m' * m⁻¹ := by rw [← h']; group
    have := hfix _ (N.mul_mem hm' (N.inv_mem hm)) hfx
    exact Subtype.ext (mul_inv_eq_one.mp this).symm
  intro n hn
  obtain ⟨⟨m, hm⟩, hmn⟩ := (Finite.injective_iff_surjective.mp hκ) ⟨n, hn⟩
  have hn' : n = m⁻¹ * τ m := (congrArg Subtype.val hmn).symm
  rw [hn', map_mul, map_inv, hτ]
  group

theorem odd_card_of_fixedPoints {N : Subgroup Γ} [Finite N] (τ : Γ →* Γ)
    (hτ : ∀ g, τ (τ g) = g) (hN : ∀ n ∈ N, τ n ∈ N) (hfix : ∀ n ∈ N, τ n = n → n = 1) :
    Odd (Nat.card N) := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨n, hn⟩, hord⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
  have hinv := inv_of_fixedPoints τ hτ hN hfix n hn
  have hsq : n * n = 1 := by
    have := pow_orderOf_eq_one (⟨n, hn⟩ : N)
    rw [hord, sq] at this
    exact congrArg Subtype.val this
  have hn1 : n = 1 := hfix n hn (by rw [hinv, inv_eq_of_mul_eq_one_right hsq])
  have : (⟨n, hn⟩ : N) = 1 := Subtype.ext hn1
  rw [this, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem commute_inv_mul_of_inv {N : Subgroup Γ} [N.Normal] (τ : Γ →* Γ)
    (hinv : ∀ n ∈ N, τ n = n⁻¹) (x : Γ) {n : Γ} (hn : n ∈ N) : Commute (x⁻¹ * τ x) n := by
  have hc : x * n * x⁻¹ ∈ N := ‹N.Normal›.conj_mem n hn x
  have h1 := hinv _ hc
  rw [map_mul, map_mul, map_inv, hinv n hn] at h1
  have h2 : (x⁻¹ * τ x) * n⁻¹ = n⁻¹ * (x⁻¹ * τ x) := by
    have h3 : τ x * n⁻¹ * (τ x)⁻¹ = x * n⁻¹ * x⁻¹ := by rw [h1]; group
    calc (x⁻¹ * τ x) * n⁻¹ = x⁻¹ * (τ x * n⁻¹ * (τ x)⁻¹) * τ x := by group
      _ = n⁻¹ * (x⁻¹ * τ x) := by rw [h3]; group
  have := (Commute.inv_right (a := x⁻¹ * τ x) (b := n⁻¹) h2)
  rwa [inv_inv] at this

end FixedPoints

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
