module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LieType.Universal.Unitary Matrix

section Gram

variable {F : Type} [Field F] (σ bar : F ≃+* F) {n : ℕ}

theorem conjTr_smul' (a : F) (X : Matrix (Fin n) (Fin n) F) :
    conjTr bar (a • X) = bar a • conjTr bar X := by
  ext i j
  simp [conjTr]

theorem conjTr_map' (h : ∀ x, σ (bar x) = bar (σ x)) (X : Matrix (Fin n) (Fin n) F) :
    conjTr bar (X.map σ) = (conjTr bar X).map σ := by
  ext i j
  simp [conjTr, h]

theorem conjTr_conjTr' (h : ∀ x, bar (bar x) = x) (X : Matrix (Fin n) (Fin n) F) :
    conjTr bar (conjTr bar X) = X := by
  ext i j
  simp [conjTr, h]

theorem map_smul_σ (a : F) (X : Matrix (Fin n) (Fin n) F) : (a • X).map σ = σ a • X.map σ := by
  ext i j
  simp

variable {σ bar}

theorem map_gram (hc : ∀ x, σ (bar x) = bar (σ x)) {A H : Matrix (Fin n) (Fin n) F} {d : F}
    (hA : conjTr bar A * A = 1) (hH : A * H.map σ = d • H) :
    (conjTr bar H * H).map σ = (bar d * d) • (conjTr bar H * H) := by
  have h1 : conjTr bar (A * H.map σ) = conjTr bar (d • H) := by rw [hH]
  rw [conjTr_mul, conjTr_smul'] at h1
  have e : (conjTr bar H * H).map σ = conjTr bar (H.map σ) * H.map σ := by
    rw [Matrix.map_mul, conjTr_map' σ bar hc]
  rw [e]
  calc conjTr bar (H.map σ) * H.map σ
      = conjTr bar (H.map σ) * (conjTr bar A * A) * H.map σ := by rw [hA, Matrix.mul_one]
    _ = (conjTr bar (H.map σ) * conjTr bar A) * (A * H.map σ) := by
        simp only [Matrix.mul_assoc]
    _ = (bar d • conjTr bar H) * (d • H) := by rw [h1, hH]
    _ = (bar d * d) • (conjTr bar H * H) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem norm_eq_one_of_map_eq (h3 : ∀ x, σ (σ (σ x)) = x) {J : Matrix (Fin 3) (Fin 3) F} {μ : F}
    (hJ : J.map σ = μ • J) (hdet : J.det ≠ 0) : μ * σ μ * σ (σ μ) = 1 := by
  have h2 : (J.map σ).map σ = σ μ • (μ • J) := by rw [hJ, map_smul_σ, hJ]
  have h3' : ((J.map σ).map σ).map σ = σ (σ μ) • (σ μ • (μ • J)) := by
    rw [h2, map_smul_σ, map_smul_σ, hJ]
  have h4 : ((J.map σ).map σ).map σ = J := by
    ext i j
    simp [h3]
  obtain ⟨i, j, hij⟩ : ∃ i j, J i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hdet
    have : J = 0 := Matrix.ext hcon
    rw [this]
    simp
  have h5 := congrFun (congrFun (h4.symm.trans h3') i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h5
  have h6 : (μ * σ μ * σ (σ μ)) * J i j = 1 * J i j := by linear_combination -h5
  exact mul_right_cancel₀ hij h6

end Gram

end CFSG.HardMathSupport.Solomon.Coordinator
