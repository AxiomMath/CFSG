module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinCen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpProof

open Matrix

section Torus

variable (F : Type) [Field F] [CharP F 2]

theorem two_eq_zero_F : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2

theorem sq_eq_one_F {a : F} (h : a ^ 2 = 1) : a = 1 := by
  have h2 := two_eq_zero_F F
  have : (a - 1) ^ 2 = 0 := by linear_combination h + (1 - a) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)

@[expose] def tm (α β : F) : Matrix (Fin 2) (Fin 2) F := !![α, β; β, α + β]

@[expose] def Nrm (α β : F) : F := α ^ 2 + α * β + β ^ 2

variable {F}

theorem tm_mul (α β α' β' : F) :
    tm F α β * tm F α' β' = tm F (α * α' + β * β') (α * β' + β * α' + β * β') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem tm_one : tm F 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm]

theorem tm_transpose (α β : F) : (tm F α β)ᵀ = tm F α β := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tm]

theorem det_tm (α β : F) : (tm F α β).det = Nrm F α β := by
  have h2 := two_eq_zero_F F
  simp only [Matrix.det_fin_two, tm, Nrm]
  simp
  linear_combination (-(β ^ 2)) * h2

theorem Nrm_mul (α β α' β' : F) :
    Nrm F (α * α' + β * β') (α * β' + β * α' + β * β') = Nrm F α β * Nrm F α' β' := by
  rw [← det_tm, ← det_tm, ← det_tm, ← Matrix.det_mul, tm_mul]

theorem tm_symp (α β : F) :
    (tm F α β)ᵀ * !![0, 1; 1, 0] * tm F α β = Nrm F α β • !![0, 1; 1, 0] := by
  have h2 := two_eq_zero_F F
  rw [tm_transpose]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [tm, Nrm, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (α * β) * h2
  · simp [tm, Nrm, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [tm, Nrm, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [tm, Nrm, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination ((α + β) * β) * h2

@[expose] def Tall (F : Type) [Field F] [CharP F 2] : Subgroup (GL (Fin 2) F) where
  carrier := {g | ∃ α β : F, Nrm F α β = 1 ∧ (g : Matrix (Fin 2) (Fin 2) F) = tm F α β}
  one_mem' := ⟨1, 0, by simp [Nrm], by rw [Units.val_one, tm_one]⟩
  mul_mem' := by
    rintro g h ⟨α, β, hn, hg⟩ ⟨α', β', hn', hh⟩
    refine ⟨α * α' + β * β', α * β' + β * α' + β * β', ?_, ?_⟩
    · rw [Nrm_mul, hn, hn', one_mul]
    · rw [Units.val_mul, hg, hh, tm_mul]
  inv_mem' := by
    rintro g ⟨α, β, hn, hg⟩
    have h2 := two_eq_zero_F F
    have hprod' : tm F (α + β) β * tm F α β = 1 := by
      have e1 : (α + β) * α + β * β = Nrm F α β := by simp only [Nrm]; ring
      have e2 : (α + β) * β + β * α + β * β = 0 := by linear_combination (α * β + β ^ 2) * h2
      rw [tm_mul, e1, e2, hn, tm_one]
    refine ⟨α + β, β, ?_, ?_⟩
    · have : Nrm F (α + β) β = Nrm F α β := by
        simp only [Nrm]
        linear_combination (α * β + β ^ 2) * h2
      rw [this, hn]
    · have h1 : (g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          1 := g.mul_inv
      rw [hg] at h1
      exact (left_inv_eq_right_inv hprod' h1).symm

end Torus

end K421SpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
