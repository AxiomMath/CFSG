module

public import CFSG.LieType.SeitzGeneration.SpF2.Core

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_swap_char2 [CharP K 2] {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) : eichler Q w u = eichler Q u w := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hneg : ∀ v : V, -v = v := fun v =>
    neg_eq_iff_add_eq_zero.mpr (by rw [← two_smul K v, h2K, zero_smul])
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hw hwu, eichler_apply hu huw, hu, hw, zero_mul, zero_mul, add_zero, add_zero,
    sub_eq_add_neg, sub_eq_add_neg, hneg (polar Q x u • w), hneg (polar Q x w • u)]
  abel

@[expose] def pairDet (Q : QuadraticForm K V) (c₁ c₂ u v : V) : K :=
  polar Q u c₁ * polar Q v c₂ - polar Q u c₂ * polar Q v c₁

theorem linearIndependent_of_pairDet_ne {x y c₁ c₂ : V} (hΔ : pairDet Q c₁ c₂ x y ≠ 0) :
    LinearIndependent K ![x, y] ∧ LinearIndependent K ![c₁, c₂] := by
  unfold pairDet at hΔ
  constructor
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrArg (fun v => polar Q v c₁) hst
    have e2 := congrArg (fun v => polar Q v c₂) hst
    simp only [polar_add_left, polar_smul_left_eq, polar_zero_left] at e1 e2
    constructor
    · have h : s * (polar Q x c₁ * polar Q y c₂ - polar Q x c₂ * polar Q y c₁) = 0 := by
        linear_combination polar Q y c₂ * e1 - polar Q y c₁ * e2
      exact (mul_eq_zero.mp h).resolve_right hΔ
    · have h : t * (polar Q x c₁ * polar Q y c₂ - polar Q x c₂ * polar Q y c₁) = 0 := by
        linear_combination polar Q x c₁ * e2 - polar Q x c₂ * e1
      exact (mul_eq_zero.mp h).resolve_right hΔ
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := congrArg (fun v => polar Q x v) hst
    have e2 := congrArg (fun v => polar Q y v) hst
    simp only [polar_add_right, polar_smul_right_eq, polar_zero_right] at e1 e2
    constructor
    · have h : s * (polar Q x c₁ * polar Q y c₂ - polar Q x c₂ * polar Q y c₁) = 0 := by
        linear_combination polar Q y c₂ * e1 - polar Q x c₂ * e2
      exact (mul_eq_zero.mp h).resolve_right hΔ
    · have h : t * (polar Q x c₁ * polar Q y c₂ - polar Q x c₂ * polar Q y c₁) = 0 := by
        linear_combination polar Q x c₁ * e2 - polar Q y c₁ * e1
      exact (mul_eq_zero.mp h).resolve_right hΔ

private theorem radical_coeffs_aux {a b c d e f : K} (hΔ : a * d - b * c ≠ 0) :
    e + (c * f - d * e) / (a * d - b * c) * a + (e * b - f * a) / (a * d - b * c) * c = 0 ∧
    f + (c * f - d * e) / (a * d - b * c) * b + (e * b - f * a) / (a * d - b * c) * d = 0 := by
  have hα := div_mul_cancel₀ (c * f - d * e) hΔ
  have hβ := div_mul_cancel₀ (e * b - f * a) hΔ
  constructor
  · apply mul_right_cancel₀ hΔ
    linear_combination a * hα + c * hβ
  · apply mul_right_cancel₀ hΔ
    linear_combination b * hα + d * hβ

theorem polar_radical_vector {x y z c₁ c₂ : V} (hΔ : pairDet Q c₁ c₂ x y ≠ 0) :
    polar Q (z + (pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y) • x +
      (pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y) • y) c₁ = 0 ∧
    polar Q (z + (pairDet Q c₁ c₂ y z / pairDet Q c₁ c₂ x y) • x +
      (pairDet Q c₁ c₂ z x / pairDet Q c₁ c₂ x y) • y) c₂ = 0 := by
  unfold pairDet at hΔ ⊢
  simp only [polar_add_left, polar_smul_left_eq]
  exact radical_coeffs_aux hΔ

structure TwistClosed (Y : Set (Matrix (Fin 2) (Fin 2) K × SpecialLinearGroup (Fin 2) K)) :
    Prop where
  one_mem : ((0 : Matrix (Fin 2) (Fin 2) K), (1 : SpecialLinearGroup (Fin 2) K)) ∈ Y
  mul_mem : ∀ {X X' : Matrix (Fin 2) (Fin 2) K} {A A' : SpecialLinearGroup (Fin 2) K},
    (X, A) ∈ Y → (X', A') ∈ Y → (X + (A : Matrix (Fin 2) (Fin 2) K) * X', A * A') ∈ Y
  inv_mem : ∀ {X : Matrix (Fin 2) (Fin 2) K} {A : SpecialLinearGroup (Fin 2) K},
    (X, A) ∈ Y →
      (-(((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X), A⁻¹) ∈ Y

theorem eq_zero_or_eq_one_of_card_two' {k : Subfield K} (hk : Nat.card k = 2) {c : K}
    (hc : c ∈ k) : c = 0 ∨ c = 1 :=
  SpF2.eq_zero_or_eq_one_of_card_two hk hc

theorem charP_two_of_subfield_card_two {k : Subfield K} (hk : Nat.card k = 2) : CharP K 2 := by
  rcases SpF2.eq_zero_or_eq_one_of_card_two hk (k.add_mem k.one_mem k.one_mem) with h | h
  · exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by push_cast; linear_combination h)
  · exact absurd (by linear_combination h : (1 : K) = 0) one_ne_zero

end CFSG.LieType.SeitzGeneration.OmegaF2
