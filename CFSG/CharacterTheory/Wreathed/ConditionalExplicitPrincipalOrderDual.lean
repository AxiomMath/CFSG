module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

section Dual

variable {T : Type*} [Group T] [Finite T] (hcomm : ∀ a b : T, a * b = b * a)
include hcomm

theorem exists_hom_units_apply_ne_one {g : T} (hg : g ≠ 1) : ∃ θ : T →* ℂˣ, θ g ≠ 1 := by
  let _ : CommGroup T := { (inferInstance : Group T) with mul_comm := hcomm }
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := Additive T)
    (a := Additive.ofMul g)).mpr (by simpa using hg)
  refine ⟨(ψ.toMonoidHom).toHomUnits, ?_⟩
  intro h
  apply hψ
  have h1 := congrArg Units.val h
  exact h1

omit hcomm in
theorem units_eq_one_or_neg_one_of_sq {u : ℂˣ} (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  have h : ((u : ℂ) - 1) * ((u : ℂ) + 1) = 0 := by
    have h1 := congrArg Units.val hu
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h1
    linear_combination h1
  rcases mul_eq_zero.mp h with h2 | h2
  · left
    exact Units.ext (by rw [Units.val_one]; linear_combination h2)
  · right
    exact Units.ext (by rw [Units.val_neg, Units.val_one]; linear_combination h2)

omit hcomm in
theorem exists_two_pow_orderOf_mul {M : Type*} [CommMonoid M] {a b : M} {i j : ℕ}
    (ha : orderOf a = 2 ^ i) (hb : orderOf b = 2 ^ j) : ∃ k : ℕ, orderOf (a * b) = 2 ^ k := by
  have ha1 : a ^ (2 ^ (i + j)) = 1 := by
    rw [pow_add, pow_mul, ← ha, pow_orderOf_eq_one, one_pow]
  have hb1 : b ^ (2 ^ (i + j)) = 1 := by
    rw [add_comm, pow_add, pow_mul, ← hb, pow_orderOf_eq_one, one_pow]
  have h : (a * b) ^ (2 ^ (i + j)) = 1 := by rw [mul_pow, ha1, hb1, one_mul]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  exact ⟨k, hk⟩

theorem exists_two_pow_hom_units_apply_eq_neg_one {g : T} (hg2 : g ^ 2 = 1) (hg : g ≠ 1) :
    ∃ θ : T →* ℂˣ, (∃ k : ℕ, orderOf θ = 2 ^ k) ∧ θ g = -1 := by
  obtain ⟨θ₀, hθ₀⟩ := exists_hom_units_apply_ne_one hcomm hg
  have hneg : θ₀ g = -1 := by
    rcases units_eq_one_or_neg_one_of_sq (show θ₀ g ^ 2 = 1 by rw [← map_pow, hg2, map_one]) with
      h | h
    · exact absurd h hθ₀
    · exact h
  set N := Nat.card T with hN
  have hN0 : N ≠ 0 := Nat.card_pos.ne'
  set v := N.factorization 2 with hv
  set o := N / 2 ^ v with ho
  have hodd : Odd o := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Nat.not_dvd_ordCompl Nat.prime_two hN0
  have hNo : 2 ^ v * o = N := Nat.mul_div_cancel' (Nat.ordProj_dvd _ _)
  refine ⟨θ₀ ^ o, ?_, ?_⟩
  · have h : (θ₀ ^ o) ^ (2 ^ v) = 1 := by
      refine MonoidHom.ext fun t => ?_
      rw [MonoidHom.pow_apply, MonoidHom.pow_apply, ← pow_mul, Nat.mul_comm o, hNo, ← map_pow,
        pow_card_eq_one', map_one, MonoidHom.one_apply]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
    exact ⟨k, hk⟩
  · rw [MonoidHom.pow_apply, hneg, hodd.neg_one_pow]

variable [Fintype (T →* ℂˣ)]

theorem sum_two_pow_hom_units_apply_eq_zero {g : T} (hg2 : g ^ 2 = 1) (hg : g ≠ 1) :
    ∑ θ ∈ Finset.univ.filter (fun θ : T →* ℂˣ => ∃ k : ℕ, orderOf θ = 2 ^ k), (θ g : ℂ) = 0 := by
  obtain ⟨θ₁, ⟨i, hi⟩, hθ₁⟩ := exists_two_pow_hom_units_apply_eq_neg_one hcomm hg2 hg
  set S := Finset.univ.filter (fun θ : T →* ℂˣ => ∃ k : ℕ, orderOf θ = 2 ^ k) with hS
  have hmem : ∀ θ, θ ∈ S ↔ ∃ k : ℕ, orderOf θ = 2 ^ k := fun θ => by simp [hS]
  have hi' : orderOf θ₁⁻¹ = 2 ^ i := (orderOf_inv θ₁).trans hi
  have hsum : ∑ θ ∈ S, (θ g : ℂ) = ∑ θ ∈ S, ((θ₁ * θ) g : ℂ) := by
    refine (Finset.sum_nbij' (fun θ => θ₁ * θ) (fun θ => θ₁⁻¹ * θ) ?_ ?_ ?_ ?_ ?_).symm
    · intro θ hθ
      obtain ⟨j, hj⟩ := (hmem θ).mp hθ
      exact (hmem _).mpr (exists_two_pow_orderOf_mul hi hj)
    · intro θ hθ
      obtain ⟨j, hj⟩ := (hmem θ).mp hθ
      exact (hmem _).mpr (exists_two_pow_orderOf_mul hi' hj)
    · intro θ _
      exact inv_mul_cancel_left θ₁ θ
    · intro θ _
      exact mul_inv_cancel_left θ₁ θ
    · intro θ _
      rfl
  have h2 : ∑ θ ∈ S, ((θ₁ * θ) g : ℂ) = -∑ θ ∈ S, (θ g : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [MonoidHom.mul_apply, hθ₁, Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]
  rw [h2] at hsum
  linear_combination hsum / 2

theorem sum_two_pow_hom_units_add_sq {t t' : T} (ht : t ^ 2 = 1) (ht' : t' ^ 2 = 1)
    (htt' : t ≠ t') :
    ∑ θ ∈ Finset.univ.filter (fun θ : T →* ℂˣ => ∃ k : ℕ, orderOf θ = 2 ^ k),
      ((θ t : ℂ) + θ t') ^ 2 =
      2 * (Finset.univ.filter (fun θ : T →* ℂˣ => ∃ k : ℕ, orderOf θ = 2 ^ k)).card := by
  have hg2 : (t * t') ^ 2 = 1 := by
    rw [(show Commute t t' from hcomm t t').mul_pow, ht, ht', one_mul]
  have htinv : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ht]
  have hg : t * t' ≠ 1 := by
    intro h
    apply htt'
    rw [← htinv]
    exact (eq_inv_of_mul_eq_one_right h).symm
  have hterm : ∀ θ : T →* ℂˣ, ((θ t : ℂ) + θ t') ^ 2 = 2 + 2 * (θ (t * t') : ℂ) := by
    intro θ
    have h1 : (θ t : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ht, map_one, Units.val_one]
    have h2 : (θ t' : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, ht', map_one, Units.val_one]
    rw [map_mul, Units.val_mul]
    linear_combination h1 + h2
  rw [Finset.sum_congr rfl fun θ _ => hterm θ, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_two_pow_hom_units_apply_eq_zero hcomm hg2 hg, Finset.sum_const, nsmul_eq_mul]
  ring

end Dual

section Pairs

theorem sum_comp_eq_two_mul_sum_image {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (w : α → α) (S : Finset α) (hS : ∀ P ∈ S, w P ∈ S ∧ w P ≠ P)
    (hf : ∀ P ∈ S, ∀ Q ∈ S, f P = f Q ↔ Q = P ∨ Q = w P) (g : β → ℂ) :
    ∑ P ∈ S, g (f P) = 2 * ∑ b ∈ S.image f, g b := by
  rw [Finset.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hb
  have hfil : S.filter (fun P => f P = f P₀) = {P₀, w P₀} := by
    ext Q
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hQ, hQf⟩
      exact (hf P₀ hP₀ Q hQ).mp hQf.symm
    · rintro (rfl | rfl)
      · exact ⟨hP₀, rfl⟩
      · exact ⟨(hS P₀ hP₀).1, ((hf P₀ hP₀ (w P₀) (hS P₀ hP₀).1).mpr (Or.inr rfl)).symm⟩
  rw [hfil, Finset.card_pair (hS P₀ hP₀).2.symm, nsmul_eq_mul]
  norm_num

end Pairs

end CFSG.Wreathed
