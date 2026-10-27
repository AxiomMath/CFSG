module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix

section Ext

variable {K : Type*} [Field K] {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι']

@[expose] def extMat (E : Matrix ι' ι K) (G : Matrix ι ι K) : Matrix ι' ι' K :=
  1 + E * (G - 1) * Eᵀ

theorem extMat_one (E : Matrix ι' ι K) : extMat E 1 = 1 := by
  simp [extMat]

theorem extMat_mul {E : Matrix ι' ι K} (hE : Eᵀ * E = 1) (G H : Matrix ι ι K) :
    extMat E G * extMat E H = extMat E (G * H) := by
  have key : (E * (G - 1) * Eᵀ) * (E * (H - 1) * Eᵀ) = E * ((G - 1) * (H - 1)) * Eᵀ := by
    calc (E * (G - 1) * Eᵀ) * (E * (H - 1) * Eᵀ)
        = E * (G - 1) * (Eᵀ * E) * (H - 1) * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = E * ((G - 1) * (H - 1)) * Eᵀ := by
        rw [hE, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
  have h2 : E * (G * H - 1) * Eᵀ =
      E * (G - 1) * Eᵀ + E * (H - 1) * Eᵀ + E * ((G - 1) * (H - 1)) * Eᵀ := by
    have : G * H - 1 = (G - 1) + (H - 1) + (G - 1) * (H - 1) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [this, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  unfold extMat
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  rw [key, h2]
  abel

theorem extMat_comm {E₁ E₂ : Matrix ι' ι K} (h12 : E₁ᵀ * E₂ = 0) (G H : Matrix ι ι K) :
    extMat E₁ G * extMat E₂ H = extMat E₂ H * extMat E₁ G := by
  have h21 : E₂ᵀ * E₁ = 0 := by
    have := congrArg Matrix.transpose h12
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this
  have k1 : (E₁ * (G - 1) * E₁ᵀ) * (E₂ * (H - 1) * E₂ᵀ) = 0 := by
    calc (E₁ * (G - 1) * E₁ᵀ) * (E₂ * (H - 1) * E₂ᵀ)
        = E₁ * (G - 1) * (E₁ᵀ * E₂) * (H - 1) * E₂ᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h12]; simp
  have k2 : (E₂ * (H - 1) * E₂ᵀ) * (E₁ * (G - 1) * E₁ᵀ) = 0 := by
    calc (E₂ * (H - 1) * E₂ᵀ) * (E₁ * (G - 1) * E₁ᵀ)
        = E₂ * (H - 1) * (E₂ᵀ * E₁) * (G - 1) * E₁ᵀ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h21]; simp
  unfold extMat
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  rw [k1, k2]
  abel

theorem extMat_retract {E₁ E₂ : Matrix ι' ι K} (h11 : E₁ᵀ * E₁ = 1) (h21 : E₂ᵀ * E₁ = 0)
    (G H : Matrix ι ι K) : E₁ᵀ * (extMat E₁ G * extMat E₂ H) * E₁ = G := by
  have k : (E₁ * (G - 1) * E₁ᵀ) * (E₂ * (H - 1) * E₂ᵀ) * E₁ = 0 := by
    calc (E₁ * (G - 1) * E₁ᵀ) * (E₂ * (H - 1) * E₂ᵀ) * E₁
        = E₁ * (G - 1) * E₁ᵀ * E₂ * (H - 1) * (E₂ᵀ * E₁) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h21]; simp
  have k' : (E₂ * (H - 1) * E₂ᵀ) * E₁ = 0 := by
    calc (E₂ * (H - 1) * E₂ᵀ) * E₁ = E₂ * (H - 1) * (E₂ᵀ * E₁) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h21]; simp
  have k'' : E₁ᵀ * (E₁ * (G - 1) * E₁ᵀ) * E₁ = G - 1 := by
    calc E₁ᵀ * (E₁ * (G - 1) * E₁ᵀ) * E₁ = (E₁ᵀ * E₁) * (G - 1) * (E₁ᵀ * E₁) := by
          simp only [Matrix.mul_assoc]
      _ = G - 1 := by rw [h11]; simp
  unfold extMat
  calc E₁ᵀ * ((1 + E₁ * (G - 1) * E₁ᵀ) * (1 + E₂ * (H - 1) * E₂ᵀ)) * E₁
      = E₁ᵀ * E₁ + E₁ᵀ * (E₁ * (G - 1) * E₁ᵀ) * E₁ +
          (E₁ᵀ * (E₂ * (H - 1) * E₂ᵀ * E₁) + E₁ᵀ * ((E₁ * (G - 1) * E₁ᵀ) * (E₂ * (H - 1) * E₂ᵀ)
            * E₁)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_assoc]
    _ = G := by
        rw [k', k, h11, k'']
        simp

theorem extMat_map {L : Type*} [Field L] (φ : K →+* L) {E : Matrix ι' ι K} {E' : Matrix ι' ι L}
    (hE : E.map φ = E') (G : Matrix ι ι K) : (extMat E G).map φ = extMat E' (G.map φ) := by
  unfold extMat
  rw [← hE]
  simp [Matrix.map_add, Matrix.map_mul, Matrix.map_sub, Matrix.transpose_map, Matrix.map_one φ
    (map_zero φ) (map_one φ)]

@[expose] noncomputable def extGL {E : Matrix ι' ι K} (hE : Eᵀ * E = 1) : GL ι K →* GL ι' K where
  toFun g := ⟨extMat E (g : Matrix ι ι K), extMat E ((g⁻¹ : GL ι K) : Matrix ι ι K),
    by rw [extMat_mul hE, ← Units.val_mul, mul_inv_cancel, Units.val_one, extMat_one],
    by rw [extMat_mul hE, ← Units.val_mul, inv_mul_cancel, Units.val_one, extMat_one]⟩
  map_one' := Units.ext (by simp [extMat_one])
  map_mul' g h := Units.ext (by
    change extMat E ((g * h : GL ι K) : Matrix ι ι K) = extMat E g * extMat E h
    rw [Units.val_mul, extMat_mul hE])

theorem extGL_comm {E₁ E₂ : Matrix ι' ι K} (h₁ : E₁ᵀ * E₁ = 1) (h₂ : E₂ᵀ * E₂ = 1)
    (h12 : E₁ᵀ * E₂ = 0) (g h : GL ι K) : extGL h₁ g * extGL h₂ h = extGL h₂ h * extGL h₁ g :=
  Units.ext (extMat_comm h12 _ _)

theorem extGL_retract {E₁ E₂ : Matrix ι' ι K} (h₁ : E₁ᵀ * E₁ = 1) (h₂ : E₂ᵀ * E₂ = 1)
    (h21 : E₂ᵀ * E₁ = 0) (g h : GL ι K) :
    E₁ᵀ * ((extGL h₁ g * extGL h₂ h : GL ι' K) : Matrix ι' ι' K) * E₁ = (g : Matrix ι ι K) :=
  extMat_retract h₁ h21 _ _

end Ext

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
