module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLGen

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP

variable {n : ℕ} {K : Type} [Field K]

@[expose] def blockHom (E : Matrix (Fin n) (Fin 2) K) (F : Matrix (Fin 2) (Fin n) K)
    (hFE : F * E = 1) : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin n) K where
  toFun g := ⟨1 + E * ((g : Matrix (Fin 2) (Fin 2) K) - 1) * F, by
    rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hFE, Matrix.mul_one,
      add_sub_cancel]
    exact g.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Subtype.ext
    show 1 + E * ((g : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K) - 1) * F =
      (1 + E * ((g : Matrix (Fin 2) (Fin 2) K) - 1) * F) *
        (1 + E * ((h : Matrix (Fin 2) (Fin 2) K) - 1) * F)
    obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) K, X = (g : Matrix (Fin 2) (Fin 2) K) - 1 :=
      ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin 2) (Fin 2) K, Y = (h : Matrix (Fin 2) (Fin 2) K) - 1 :=
      ⟨_, rfl⟩
    have hgh : (g : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K) - 1 =
        X + Y + X * Y := by
      rw [hX, hY]
      noncomm_ring
    have key : E * X * F * (E * Y * F) = E * (X * Y) * F := by
      calc E * X * F * (E * Y * F) = E * X * (F * E) * Y * F := by simp only [Matrix.mul_assoc]
        _ = E * (X * Y) * F := by rw [hFE, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [← hX, ← hY, hgh]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, key]
    abel

theorem blockHom_coe (E : Matrix (Fin n) (Fin 2) K) (F : Matrix (Fin 2) (Fin n) K)
    (hFE : F * E = 1) (g : SpecialLinearGroup (Fin 2) K) :
    (blockHom E F hFE g : Matrix (Fin n) (Fin n) K) =
      1 + E * ((g : Matrix (Fin 2) (Fin 2) K) - 1) * F := rfl

section Pair

variable {a b : Fin n} {u φ : Fin n → K}

@[expose] def rowsF (a b : Fin n) (u φ : Fin n → K) : Matrix (Fin 2) (Fin n) K :=
  rows ((φ a)⁻¹ • φ) ((u b)⁻¹ • (Pi.single b 1 : Fin n → K))

theorem rowsF_mul_colPair (hab : a ≠ b) (hφu : φ ⬝ᵥ u = 0) (hα : u b ≠ 0) (hβ : φ a ≠ 0) :
    rowsF a b u φ * colPair a u = 1 := by
  rw [rowsF, mul_colPair]
  ext r c
  fin_cases r <;> fin_cases c <;> simp [smul_dotProduct, hφu, hα, hβ, hab]

theorem blockHom_u2 (hab : a ≠ b) (hφu : φ ⬝ᵥ u = 0) (hα : u b ≠ 0) (hβ : φ a ≠ 0) (τ : K) :
    blockHom (colPair a u) (rowsF a b u φ) (rowsF_mul_colPair hab hφu hα hβ) (u2 τ) =
      SpecialLinearGroup.transvection hab (τ * (u b)⁻¹) := by
  apply Subtype.ext
  rw [blockHom_coe, transvection_eq_tv hab, tv_coe, u2_coe]
  have h1 : (!![1, τ; 0, 1] : Matrix (Fin 2) (Fin 2) K) - 1 = !![0, τ; 0, 0] := by
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  have h2 : (!![0, τ; 0, 0] : Matrix (Fin 2) (Fin 2) K) * rowsF a b u φ =
      rows (τ • ((u b)⁻¹ • (Pi.single b 1 : Fin n → K))) 0 := by
    ext r m
    fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, rowsF, rows]
  rw [h1, Matrix.mul_assoc, h2, colPair_mul]
  simp [smul_smul]

theorem blockHom_l2 (hab : a ≠ b) (hφu : φ ⬝ᵥ u = 0) (hα : u b ≠ 0) (hβ : φ a ≠ 0) (σ : K) :
    blockHom (colPair a u) (rowsF a b u φ) (rowsF_mul_colPair hab hφu hα hβ) (l2 σ) =
      tv u ((σ * (φ a)⁻¹) • φ) (by rw [smul_dotProduct, hφu, smul_zero]) := by
  apply Subtype.ext
  rw [blockHom_coe, tv_coe, l2_coe]
  have h1 : (!![1, 0; σ, 1] : Matrix (Fin 2) (Fin 2) K) - 1 = !![0, 0; σ, 0] := by
    ext r c
    fin_cases r <;> fin_cases c <;> simp
  have h2 : (!![0, 0; σ, 0] : Matrix (Fin 2) (Fin 2) K) * rowsF a b u φ =
      rows 0 (σ • ((φ a)⁻¹ • φ)) := by
    ext r m
    fin_cases r <;> simp [Matrix.mul_apply, Fin.sum_univ_two, rowsF, rows]
  rw [h1, Matrix.mul_assoc, h2, colPair_mul]
  simp [smul_smul]

end Pair

end CFSG.LieType.SeitzGeneration
