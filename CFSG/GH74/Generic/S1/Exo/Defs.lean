module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module QuadraticMap CFSG.Open
open scoped Matrix

section Form

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

@[expose] noncomputable def soForm (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) :=
  TauCeti.QuadraticMap.orthogonalGroup Q ⊓ (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).ker

theorem mem_soForm_iff {Q : QuadraticForm K V} {g : V ≃ₗ[K] V} :
    g ∈ soForm Q ↔ (∀ v, Q (g v) = Q v) ∧ LinearEquiv.det g = 1 := by
  simp [soForm, TauCeti.QuadraticMap.mem_orthogonalGroup_iff, MonoidHom.mem_ker]

end Form

section Mat

variable {K : Type} [Field K]

@[expose] def soMat (G : Matrix (Fin 4) (Fin 4) K) : Subgroup (GL (Fin 4) K) where
  carrier := {k | (k : Matrix (Fin 4) (Fin 4) K)ᵀ * G * (k : Matrix (Fin 4) (Fin 4) K) = G ∧
    (k : Matrix (Fin 4) (Fin 4) K).det = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, ?_⟩
    · have : ((a * b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * G *
          ((a * b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (b : Matrix (Fin 4) (Fin 4) K)ᵀ * ((a : Matrix (Fin 4) (Fin 4) K)ᵀ * G *
            (a : Matrix (Fin 4) (Fin 4) K)) * (b : Matrix (Fin 4) (Fin 4) K) := by
        simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this, ha, hb]
    · simp [Matrix.det_mul, ha', hb']
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, ?_⟩
    · have h1 : (a : Matrix (Fin 4) (Fin 4) K) * ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
        by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have : ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * G *
          ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * ((a : Matrix (Fin 4) (Fin 4) K)ᵀ * G *
            (a : Matrix (Fin 4) (Fin 4) K)) * ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
        rw [ha]
      rw [this]
      have h2 : ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * (a : Matrix (Fin 4) (Fin 4) K)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
      calc ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * ((a : Matrix (Fin 4) (Fin 4) K)ᵀ * G *
            (a : Matrix (Fin 4) (Fin 4) K)) * ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
          = (((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * (a : Matrix (Fin 4) (Fin 4) K)ᵀ) * G *
            ((a : Matrix (Fin 4) (Fin 4) K) * ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
            simp only [Matrix.mul_assoc]
        _ = G := by rw [h2, h1]; simp
    · have h1 : (a : Matrix (Fin 4) (Fin 4) K).det * ((a⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
      rw [ha', one_mul] at h1
      exact h1

theorem mem_soMat_iff {G : Matrix (Fin 4) (Fin 4) K} {k : GL (Fin 4) K} :
    k ∈ soMat G ↔ (k : Matrix (Fin 4) (Fin 4) K)ᵀ * G * (k : Matrix (Fin 4) (Fin 4) K) = G ∧
      (k : Matrix (Fin 4) (Fin 4) K).det = 1 :=
  Iff.rfl

theorem neg_one_mem_soMat (G : Matrix (Fin 4) (Fin 4) K) : (-1 : GL (Fin 4) K) ∈ soMat G := by
  refine ⟨?_, ?_⟩
  · simp
  · simp [Matrix.det_neg]
    norm_num

end Mat

section Fixed

variable {F : Type} [Field F]

@[expose] def linAut (g : GL (Fin 4) F) : GL (Fin 4) F →* GL (Fin 4) F :=
  (MulAut.conj g).toMonoidHom.comp (Matrix.GeneralLinearGroup.inverseTranspose : GL (Fin 4) F ≃* GL (Fin 4) F).toMonoidHom

@[expose] def linFixed (g : GL (Fin 4) F) : Subgroup (GL (Fin 4) F) :=
  StatedSL 4 F ⊓ MonoidHom.eqLocus (linAut g) (MonoidHom.id _)

@[expose] def uniAut (bar : F →+* F) (g : GL (Fin 4) F) : GL (Fin 4) F →* GL (Fin 4) F :=
  (MulAut.conj g).toMonoidHom.comp (Matrix.GeneralLinearGroup.map bar : GL (Fin 4) F →* GL (Fin 4) F)

@[expose] def uniFixed (q : ℕ) (bar : F →+* F) (g : GL (Fin 4) F) : Subgroup (GL (Fin 4) F) :=
  StatedSU 4 q F ⊓ MonoidHom.eqLocus (uniAut bar g) (MonoidHom.id _)

end Fixed

end CFSG.GH74.Generic.S1.Exo
