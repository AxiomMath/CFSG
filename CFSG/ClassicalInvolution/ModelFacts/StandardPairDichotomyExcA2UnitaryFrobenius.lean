module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryTorus

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
  Matrix
open scoped MatrixGroups

section MapTv

variable {F : Type} [Field F] {F' : Type} [Field F']

theorem specialLinear_map_tv (σ : F →+* F') {n : ℕ} (i j : Fin n) (c : F) :
    Matrix.SpecialLinearGroup.map σ (tv i j c) = tv i j (σ c) := by
  by_cases h : i = j
  · subst h
    simp [tv]
  · apply Subtype.ext
    rw [tv_of_ne h, tv_of_ne h, Matrix.SpecialLinearGroup.map_apply_coe,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
    simp [Matrix.map_add, Matrix.map_one, Matrix.map_single]

end MapTv

section Frobenius

variable {τ : Tag} {θ δ : Fin τ.rank → ℤ} {k : Type} [Field k] {K₂ : Type} [Field K₂]

theorem frob_baseChange_iota (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ) (hp2 : p ≠ 2)
    (E : A2Embedding τ θ δ K₂) (j : K₂ →+* k) (σ : K₂ →+* K₂)
    (hσ : ∀ x, j (σ x) = j x ^ p ^ e) (z : SL(3, K₂)) :
    entrywiseFrobGL τ k p e (baseChangeGL j (E.ι z)) =
      baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ z)) := by
  have hodd : Odd (p ^ e) := (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hm : ∀ {m : K₂}, m * m = 1 → j m ^ p ^ e = j m := fun {m} h => by
    rcases mul_self_eq_one_iff.1 h with rfl | rfl
    · simp
    · simp [hodd.neg_pow]
  have key := hom_ext_sl3_tv (H := ModGL τ k)
    (f := (entrywiseFrobGL τ k p e).comp ((baseChangeGL j).comp E.ι))
    (g := ((baseChangeGL j).comp E.ι).comp (Matrix.SpecialLinearGroup.map σ))
    (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c => ?_)
  · exact DFunLike.congr_fun key z
  · change entrywiseFrobGL τ k p e (baseChangeGL j (E.ι (tv 0 1 c))) =
      baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ (tv 0 1 c)))
    rw [specialLinear_map_tv, E.h01, E.h01, baseChangeGL_pinnedX, baseChangeGL_pinnedX,
      entrywiseFrobGL_pinnedX, iterateFrobenius_def, map_mul, map_mul, hσ, mul_pow, hm E.sq₀]
  · change entrywiseFrobGL τ k p e (baseChangeGL j (E.ι (tv 1 0 c))) =
      baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ (tv 1 0 c)))
    rw [specialLinear_map_tv, E.h10, E.h10, baseChangeGL_pinnedX, baseChangeGL_pinnedX,
      entrywiseFrobGL_pinnedX, iterateFrobenius_def, map_mul, map_mul, hσ, mul_pow, hm E.sq₁]
  · change entrywiseFrobGL τ k p e (baseChangeGL j (E.ι (tv 1 2 c))) =
      baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ (tv 1 2 c)))
    rw [specialLinear_map_tv, E.h12, E.h12, baseChangeGL_pinnedX, baseChangeGL_pinnedX,
      entrywiseFrobGL_pinnedX, iterateFrobenius_def, map_mul, map_mul, hσ, mul_pow, hm E.sq₂]
  · change entrywiseFrobGL τ k p e (baseChangeGL j (E.ι (tv 2 1 c))) =
      baseChangeGL j (E.ι (Matrix.SpecialLinearGroup.map σ (tv 2 1 c)))
    rw [specialLinear_map_tv, E.h21, E.h21, baseChangeGL_pinnedX, baseChangeGL_pinnedX,
      entrywiseFrobGL_pinnedX, iterateFrobenius_def, map_mul, map_mul, hσ, mul_pow, hm E.sq₃]

end Frobenius

section Unitary

variable {E : Type} [Field E] [Finite E] {p e : ℕ} [Fact p.Prime] [CharP E p]

theorem map_suToSL_eq_tau (y : Su E p e 3) :
    Matrix.SpecialLinearGroup.map ((unitaryInvolution E p e : E ≃+* E) : E →+* E)
        (suToSL (unitaryInvolution E p e) 3 y) =
      sl3Tau E (suToSL (unitaryInvolution E p e) 3 y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, sl3Tau_apply]
  set Y := suToSL (unitaryInvolution E p e) 3 y with hY
  have h1 : conjTr (unitaryInvolution E p e) (suMat y) * suMat y = 1 := y.2.2
  have h2 : (Y : Matrix (Fin 3) (Fin 3) E) * ((Y⁻¹ : SL(3, E)) : Matrix (Fin 3) (Fin 3) E) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h3 : (suMat y : Matrix (Fin 3) (Fin 3) E) = Y := rfl
  rw [h3] at h1
  have h4 : ((Y : Matrix (Fin 3) (Fin 3) E).map (unitaryInvolution E p e))ᵀ =
      ((Y⁻¹ : SL(3, E)) : Matrix (Fin 3) (Fin 3) E) := by
    calc ((Y : Matrix (Fin 3) (Fin 3) E).map (unitaryInvolution E p e))ᵀ =
        ((Y : Matrix (Fin 3) (Fin 3) E).map (unitaryInvolution E p e))ᵀ *
          ((Y : Matrix (Fin 3) (Fin 3) E) * ((Y⁻¹ : SL(3, E)) : Matrix (Fin 3) (Fin 3) E)) := by
          rw [h2, mul_one]
      _ = (((Y : Matrix (Fin 3) (Fin 3) E).map (unitaryInvolution E p e))ᵀ * Y) *
          ((Y⁻¹ : SL(3, E)) : Matrix (Fin 3) (Fin 3) E) := by rw [Matrix.mul_assoc]
      _ = _ := by
          change conjTr (unitaryInvolution E p e) (Y : Matrix (Fin 3) (Fin 3) E) * Y * _ = _
          rw [h1, Matrix.one_mul]
  rw [← h4, Matrix.transpose_transpose]
  rfl

end Unitary

section FrobAlpha

variable {τ : Tag} {θ δ : Fin τ.rank → ℤ} {k : Type} [Field k] {K₂ : Type} [Field K₂]

theorem frob_alpha (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ) (hp2 : p ≠ 2)
    (E : A2Embedding τ θ δ K₂) (j : K₂ →+* k) (σ : K₂ →+* K₂)
    (hσ : ∀ x, j (σ x) = j x ^ p ^ e) {v' u' : ModGL τ k}
    (hu' : entrywiseFrobGL τ k p e v' = u' * v')
    (hτ : ∀ y : SL(3, K₂), u' * baseChangeGL j (E.ι y) * u'⁻¹ =
      baseChangeGL j (E.ι (sl3Tau K₂ y)))
    {y : SL(3, K₂)} (hy : Matrix.SpecialLinearGroup.map σ y = sl3Tau K₂ y) :
    entrywiseFrobGL τ k p e (v'⁻¹ * baseChangeGL j (E.ι y) * v') =
      v'⁻¹ * baseChangeGL j (E.ι y) * v' := by
  rw [map_mul, map_mul, map_inv, hu', frob_baseChange_iota p e hp2 E j σ hσ, hy]
  have h := hτ y
  calc (u' * v')⁻¹ * baseChangeGL j (E.ι (sl3Tau K₂ y)) * (u' * v') =
      v'⁻¹ * (u'⁻¹ * baseChangeGL j (E.ι (sl3Tau K₂ y)) * u') * v' := by group
    _ = _ := by
      rw [← h]
      group

end FrobAlpha

end CFSG.ClassicalInvolution.ModelFacts.Levi
