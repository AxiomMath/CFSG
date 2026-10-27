module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauAlg

public section

namespace CFSG.QuasithinUnique.Lin2.Five

open Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

@[expose] def rootE (R : Type*) [CommRing R] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.single ι₀ ι₂ 1

section Rank

variable {R : Type*} [CommRing R]

theorem conj_rootE_apply (A Ai : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) (i j : Fin 2 ⊕ Fin 2) :
    (A * rootE R * Ai) i j = A i ι₀ * Ai ι₂ j := by
  simp [rootE, Matrix.mul_apply, Matrix.single_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem tauMat_one_add_rootE_ι₀ι₃ : tauMat (1 + rootE R) ι₀ ι₃ = -1 := by
  simp [tauMat, tauPair, rootE, Matrix.one_apply, Matrix.single_apply]

theorem tauMat_one_add_rootE_ι₁ι₂ : tauMat (1 + rootE R) ι₁ ι₂ = 1 := by
  simp [tauMat, tauPair, rootE, Matrix.one_apply, Matrix.single_apply]

theorem tauMat_one_add_rootE_ι₀ι₂ : tauMat (1 + rootE R) ι₀ ι₂ = 0 := by
  simp [tauMat, tauPair, rootE, Matrix.one_apply, Matrix.single_apply]

theorem tauMat_one_add_rootE_ι₁ι₃ : tauMat (1 + rootE R) ι₁ ι₃ = 0 := by
  simp [tauMat, tauPair, rootE, Matrix.one_apply, Matrix.single_apply]

theorem tauMat_rootE_ne_conj [Nontrivial R] (A Ai : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (σ : R →+* R) (hA : A * Ai = 1)
    (h : tauMat (1 + rootE R) = A * (1 + rootE R).map σ * Ai) : False := by
  have hmap : (1 + rootE R).map σ = 1 + rootE R := by
    ext i j
    simp [rootE, Matrix.one_apply, Matrix.single_apply]
  rw [hmap, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hA] at h
  have h03 := congrFun (congrFun h ι₀) ι₃
  have h12 := congrFun (congrFun h ι₁) ι₂
  have h02 := congrFun (congrFun h ι₀) ι₂
  have h13 := congrFun (congrFun h ι₁) ι₃
  rw [tauMat_one_add_rootE_ι₀ι₃, Matrix.add_apply, conj_rootE_apply] at h03
  rw [tauMat_one_add_rootE_ι₁ι₂, Matrix.add_apply, conj_rootE_apply] at h12
  rw [tauMat_one_add_rootE_ι₀ι₂, Matrix.add_apply, conj_rootE_apply] at h02
  rw [tauMat_one_add_rootE_ι₁ι₃, Matrix.add_apply, conj_rootE_apply] at h13
  have e03 : (-1 : R) = A ι₀ ι₀ * Ai ι₂ ι₃ := by simpa [Matrix.one_apply] using h03
  have e12 : (1 : R) = A ι₁ ι₀ * Ai ι₂ ι₂ := by simpa [Matrix.one_apply] using h12
  have e02 : (0 : R) = A ι₀ ι₀ * Ai ι₂ ι₂ := by simpa [Matrix.one_apply] using h02
  have e13 : (0 : R) = A ι₁ ι₀ * Ai ι₂ ι₃ := by simpa [Matrix.one_apply] using h13
  have : (-1 : R) = 0 := by
    linear_combination e03 + (A ι₀ ι₀ * Ai ι₂ ι₃) * e12 - (A ι₁ ι₀ * Ai ι₂ ι₃) * e02
  exact one_ne_zero (neg_eq_zero.mp this)

theorem twist_rootE_apply (σ : R →+* R) (t : R) :
    (1 + t • rootE R : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).map σ = 1 + σ t • rootE R := by
  ext i j
  simp [rootE, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem eq_of_twist_rootE_conj (σ : R →+* R) (G Gi : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (hG : G * Gi = 1)
    (h : ∀ t : R, (1 + t • rootE R : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R).map σ =
      G * (1 + t • rootE R) * Gi) (t : R) : σ t = t := by
  have hA : ∀ s : R, σ s • rootE R = s • (G * rootE R * Gi) := by
    intro s
    have := h s
    rw [twist_rootE_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hG, Matrix.mul_smul,
      Matrix.smul_mul] at this
    exact add_left_cancel this
  have hB : G * rootE R * Gi = rootE R := by
    have := hA 1
    rw [map_one, one_smul, one_smul] at this
    exact this.symm
  have := hA t
  rw [hB] at this
  have h02 := congrFun (congrFun this ι₀) ι₂
  simpa [rootE] using h02

end Rank

end CFSG.QuasithinUnique.Lin2.Five
