module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix Module

open scoped Classical


variable {K : Type} [Field K]

theorem exists_idem_normal (e : Matrix (Fin 6) (Fin 6) K) (he : e * e = e) (hr : e.rank = 4) :
    ∃ A : Matrix.GeneralLinearGroup (Fin 6) K,
      (A : Matrix (Fin 6) (Fin 6) K) * e *
          ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        Matrix.diagonal (fun i : Fin 6 => if (i : ℕ) < 4 then (1 : K) else 0) := by
  let T : Submodule K (Fin 6 → K) := LinearMap.range (Matrix.mulVecLin e)
  let M : Submodule K (Fin 6 → K) := LinearMap.ker (Matrix.mulVecLin e)
  have hmemT : ∀ v : Fin 6 → K, e *ᵥ v ∈ T := fun v => ⟨v, rfl⟩
  have hTM : IsCompl T M := by
    let f : (Fin 6 → K) →ₗ[K] T := LinearMap.codRestrict T (Matrix.mulVecLin e) hmemT
    have hf : ∀ x : T, f x = x := by
      rintro ⟨x, w, rfl⟩
      apply Subtype.ext
      show e *ᵥ (e *ᵥ w) = e *ᵥ w
      rw [Matrix.mulVec_mulVec, he]
    have h := LinearMap.isCompl_of_proj hf
    have hker : LinearMap.ker f = M := by
      ext v
      have key : f v = 0 ↔ e *ᵥ v = 0 := by
        constructor
        · intro h0
          exact congrArg Subtype.val h0
        · intro h0
          exact Subtype.ext h0
      exact key
    rw [hker] at h
    exact h
  have hT : Module.finrank K T = 4 := hr
  have hM : Module.finrank K M = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin e)
    have hrange : Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) = 4 := hr
    rw [hrange, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    show Module.finrank K (LinearMap.ker (Matrix.mulVecLin e)) = 2
    omega
  let bT : Basis (Fin 4) K T := (Module.finBasis K T).reindex (finCongr hT)
  let bM : Basis (Fin 2) K M := (Module.finBasis K M).reindex (finCongr hM)
  let bS : Basis (Fin 4 ⊕ Fin 2) K (Fin 6 → K) :=
    (bT.prod bM).map (Submodule.prodEquivOfIsCompl T M hTM)
  have hbS_inl : ∀ i : Fin 4, bS (Sum.inl i) = (bT i : Fin 6 → K) := by
    intro i
    simp [bS, Basis.map_apply, Basis.prod_apply_inl_fst]
  have hbS_inr : ∀ i : Fin 2, bS (Sum.inr i) = (bM i : Fin 6 → K) := by
    intro i
    simp [bS, Basis.map_apply, Basis.prod_apply_inr_snd]
  let e7 : Fin 6 ≃ Fin 4 ⊕ Fin 2 :=
    (finCongr (rfl : 6 = 4 + 2)).trans (finSumFinEquiv (m := 4) (n := 2)).symm
  let bV : Basis (Fin 6) K (Fin 6 → K) := bS.reindex e7.symm
  have hbV : ∀ j, bV j = bS (e7 j) := fun j => by
    simp [bV]
  have hleft : ∀ j : Fin 6, (e7 j).isLeft = decide ((j : ℕ) < 4) := by
    decide
  have hmemT : ∀ j : Fin 6, (j : ℕ) < 4 → bV j ∈ T := by
    intro j hj
    have hl := hleft j
    rw [decide_eq_true hj] at hl
    cases h : e7 j with
    | inl i =>
      rw [hbV, h, hbS_inl]
      exact (bT i).2
    | inr i =>
      rw [h] at hl
      simp at hl
  have hmemM : ∀ j : Fin 6, ¬ (j : ℕ) < 4 → bV j ∈ M := by
    intro j hj
    have hl := hleft j
    rw [decide_eq_false hj] at hl
    cases h : e7 j with
    | inl i =>
      rw [h] at hl
      simp at hl
    | inr i =>
      rw [hbV, h, hbS_inr]
      exact (bM i).2
  have hcol : ∀ j : Fin 6, e *ᵥ (bV j) =
      (if (j : ℕ) < 4 then (1 : K) else 0) • bV j := by
    intro j
    by_cases hj : (j : ℕ) < 4
    · rw [if_pos hj, one_smul]
      obtain ⟨w, hw⟩ := hmemT j hj
      have hw' : e *ᵥ w = bV j := by
        simpa [Matrix.mulVecLin_apply] using hw
      rw [← hw', Matrix.mulVec_mulVec, he]
    · rw [if_neg hj, zero_smul]
      have hM' : e *ᵥ bV j = 0 := hmemM j hj
      exact hM'
  let B : Matrix (Fin 6) (Fin 6) K := (Pi.basisFun K (Fin 6)).toMatrix bV
  let B' : Matrix (Fin 6) (Fin 6) K := bV.toMatrix (Pi.basisFun K (Fin 6))
  have hBB' : B * B' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hB'B : B' * B = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hB_apply : ∀ k j, B k j = bV j k := fun k j => by
    simp [B, Module.Basis.toMatrix_apply]
  have key : e * B = B * Matrix.diagonal (fun i : Fin 6 => if (i : ℕ) < 4 then (1 : K) else 0) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [hB_apply]
    have hc := congrFun (hcol j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hc
    rw [hc]
    ring
  let Ugl : Matrix.GeneralLinearGroup (Fin 6) K := Units.mk B B' hBB' hB'B
  refine ⟨Ugl⁻¹, ?_⟩
  have e1 : ((Ugl⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = B' := rfl
  have e2 : (((Ugl⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K))⁻¹ :
      Matrix.GeneralLinearGroup (Fin 6) K) = Ugl := inv_inv Ugl
  rw [e1, show ((((Ugl⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K))⁻¹ :
      Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = B by rw [e2]]
  rw [Matrix.mul_assoc, key, ← Matrix.mul_assoc, hB'B, Matrix.one_mul]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
