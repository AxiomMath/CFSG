module

public import CFSG.GH74.Generic.BProg.B2.GenLocL2SL
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueBHigherLinearAction Matrix
open scoped MatrixGroups

namespace GenLocL3Nine

variable {K : Type} [Field K]

theorem fieldAut_eq_one_of_twisted_commute (σ : K ≃+* K) (N : Matrix (Fin 2) (Fin 2) K)
    (hN : N.det ≠ 0)
    (h : ∀ g : SL(2, K), N * (g : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K).map σ * N) : σ = 1 := by
  have key : ∀ t : K, N * !![1, t; 0, 1] = !![1, σ t; 0, 1] * N := by
    intro t
    let gt : SL(2, K) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
    have := h gt
    convert this using 2
    ext i j; fin_cases i <;> fin_cases j <;> simp [gt]
  have k1 := key 1
  have c1 := congrFun (congrFun k1 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at c1
  have c2 := congrFun (congrFun k1 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at c2
  have hc : N 1 0 = 0 := by linear_combination c1
  have had : N 0 0 = N 1 1 := by linear_combination c2
  have hdet : N 0 0 * N 1 1 ≠ 0 := by
    rw [Matrix.det_fin_two, hc] at hN
    simpa using hN
  have ha : N 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  ext t
  have kt := key t
  have e := congrFun (congrFun kt 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  have : N 0 0 * σ t = N 0 0 * t := by
    have e' : N 0 0 * t = σ t * N 1 1 := by linear_combination e
    rw [had] at e' ⊢
    linear_combination -e'
  have := mul_left_cancel₀ ha this
  simpa using this


theorem fieldAut_eq_one_aux (σ : K ≃+* K) (S S' Dm D' : Matrix (Fin 2) (Fin 2) K) (hSS : S' * S = 1)
    (hDD : D' * Dm = 1) (hdetD : D'.det ≠ 0) (hdetS : S.det = 1)
    (key : ∀ g : SL(2, K), S * (g : Matrix (Fin 2) (Fin 2) K) * S' =
      Dm * (g : Matrix (Fin 2) (Fin 2) K).map σ * D') : σ = 1 := by
  refine fieldAut_eq_one_of_twisted_commute σ (D' * S) ?_ (fun g => ?_)
  · rw [Matrix.det_mul, hdetS, mul_one]; exact hdetD
  · have h1 := key g
    have e1 : D' * (S * (g : Matrix (Fin 2) (Fin 2) K) * S') * S = D' * S * g := by
      rw [show D' * (S * (g : Matrix (Fin 2) (Fin 2) K) * S') * S =
        D' * S * (g : Matrix (Fin 2) (Fin 2) K) * (S' * S) by simp only [Matrix.mul_assoc], hSS,
        Matrix.mul_one]
    have e2 : D' * (Dm * (g : Matrix (Fin 2) (Fin 2) K).map σ * D') * S =
        (g : Matrix (Fin 2) (Fin 2) K).map σ * (D' * S) := by
      rw [show D' * (Dm * (g : Matrix (Fin 2) (Fin 2) K).map σ * D') * S =
        (D' * Dm) * (g : Matrix (Fin 2) (Fin 2) K).map σ * (D' * S) by simp only [Matrix.mul_assoc], hDD,
        Matrix.one_mul]
    rw [← e1, h1, e2]

theorem slConj_mul_slFieldAut_not_inner [Finite K] (M : GL (Fin 2) K) {σ : K ≃+* K} (hσ : σ ≠ 1) :
    slConjugation 2 K M * GLS.IVK.Lifted.slFieldAut σ ∉
      (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range := by
  rintro ⟨s, hs⟩
  refine hσ (fieldAut_eq_one_aux σ ((s : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
    ((s⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) (M : Matrix (Fin 2) (Fin 2) K)
    ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ?_ ?_ ?_ s.2 ?_)
  · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  · rw [← Units.val_mul, inv_mul_cancel]; rfl
  · exact (Matrix.isUnits_det_units (M⁻¹)).ne_zero
  · intro g
    have := congrArg (fun φ : MulAut SL(2, K) =>
      ((φ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) hs
    simpa [MulAut.conj_apply, LinearFlag.coe_slConjugation, GLS.IVK.Lifted.slFieldAut_apply,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using this


theorem gammaAct_sl2_of_not_inner_small [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    {A : Type} [Group A] [Finite A] (β : A →* MulAut SL(2, K)) (hA : IsRank23 A)
    (hni : ¬ β.range ≤ (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range)
    (hsmall : Nat.card β.range ≤ 4) : gammaAct β = ⊤ := by
  by_cases hker : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ β.ker
  · obtain ⟨E, hE, hle⟩ := hker
    exact gammaAct_eq_top_of_le_ker β hE hle
  push Not at hker
  obtain ⟨hD, hγ, -⟩ := range_reduction β hA (fun E hE hle => hker E hE hle)
  rw [hγ]
  have : Finite ↥β.range := Finite.of_surjective _ β.rangeRestrict_surjective
  rcases hD.2 with hr2 | hr3
  · have h4 : Nat.card β.range = 4 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr2]
      norm_num
    rcases GenLocL2SL.gammaAct_sl2_core hp hp2 hK h5 hD.1 h4 β.range.subtype with h | ⟨-, hinn⟩
    · exact h
    · exfalso
      apply hni
      rwa [Subgroup.range_subtype] at hinn
  · exfalso
    have h8 : Nat.card β.range = 8 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr3]
      norm_num
    omega


end GenLocL3Nine

end CFSG.GH74.Generic.BProg.B2
