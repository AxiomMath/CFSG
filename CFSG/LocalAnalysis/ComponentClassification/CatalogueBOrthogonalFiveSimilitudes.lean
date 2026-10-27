module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix

universe u

variable {K : Type u} [Field K]

theorem symplecticGram_entry : symplecticGram K 0 2 = 1 := rfl

theorem symplecticGram_square :
    symplecticGram K * symplecticGram K = -(1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symplecticGram, Matrix.mul_apply, Fin.sum_univ_four]

theorem symplectic_multiplier_unique (A : GL (Fin 4) K) (a b : Kˣ)
    (ha : A.valᵀ * symplecticGram K * A.val = (a : K) • symplecticGram K)
    (hb : A.valᵀ * symplecticGram K * A.val = (b : K) • symplecticGram K) : a = b := by
  apply Units.ext
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 2) (ha.symm.trans hb)
  simpa [Matrix.smul_apply, smul_eq_mul, symplecticGram_entry] using h

theorem symplectic_similitude_inverse (A : GL (Fin 4) K) (a : Kˣ)
    (hA : A.valᵀ * symplecticGram K * A.val = (a : K) • symplecticGram K) :
    A⁻¹.valᵀ * symplecticGram K * A⁻¹.val = ((a⁻¹ : Kˣ) : K) • symplecticGram K := by
  have ht : A⁻¹.valᵀ * A.valᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hJ : symplecticGram K = (a : K) •
      (A⁻¹.valᵀ * symplecticGram K * A⁻¹.val) := by
    calc
      symplecticGram K = A⁻¹.valᵀ * (A.valᵀ * symplecticGram K * A.val) * A⁻¹.val := by
        calc
          symplecticGram K =
              (A⁻¹.valᵀ * A.valᵀ) * symplecticGram K * (A.val * A⁻¹.val) := by
                rw [ht, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = (a : K) • (A⁻¹.valᵀ * symplecticGram K * A⁻¹.val) := by
        rw [hA, Matrix.mul_smul, Matrix.smul_mul]
  have hm := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => ((a⁻¹ : Kˣ) : K) • M) hJ
  simpa [smul_smul] using hm.symm

@[expose] def symplecticSimilitudes (K : Type u) [Field K] : Subgroup (GL (Fin 4) K) where
  carrier := {A | ∃ a : Kˣ, A.valᵀ * symplecticGram K * A.val = (a : K) • symplecticGram K}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro A B ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    change (A.val * B.val)ᵀ * symplecticGram K * (A.val * B.val) = _
    rw [Matrix.transpose_mul]
    calc
      B.valᵀ * A.valᵀ * symplecticGram K * (A.val * B.val) =
          B.valᵀ * (A.valᵀ * symplecticGram K * A.val) * B.val := by
            simp only [Matrix.mul_assoc]
      _ = (a : K) • (B.valᵀ * symplecticGram K * B.val) := by
        rw [ha, Matrix.mul_smul, Matrix.smul_mul]
      _ = ((a * b : Kˣ) : K) • symplecticGram K := by rw [hb, smul_smul]; rfl
  inv_mem' := by
    rintro A ⟨a, ha⟩
    exact ⟨a⁻¹, symplectic_similitude_inverse A a ha⟩

@[expose] def symplecticMultiplier : symplecticSimilitudes K →* Kˣ where
  toFun A := Classical.choose A.property
  map_one' := symplectic_multiplier_unique 1 _ 1 (Classical.choose_spec (1 : symplecticSimilitudes K).property)
    (by simp)
  map_mul' A B := by
    have hA : ∃ a : Kˣ, A.val.valᵀ * symplecticGram K * A.val.val = (a : K) • symplecticGram K :=
      A.property
    have hB : ∃ b : Kˣ, B.val.valᵀ * symplecticGram K * B.val.val = (b : K) • symplecticGram K :=
      B.property
    apply symplectic_multiplier_unique (A.val * B.val)
    · exact Classical.choose_spec (A * B).property
    · calc
        (A.val * B.val).valᵀ * symplecticGram K * (A.val * B.val).val =
            B.val.valᵀ * (A.val.valᵀ * symplecticGram K * A.val.val) * B.val.val := by
              simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = ((Classical.choose hA : Kˣ) : K) •
            (B.val.valᵀ * symplecticGram K * B.val.val) := by
              conv_lhs => rw [Classical.choose_spec hA, Matrix.mul_smul, Matrix.smul_mul]
        _ = ((Classical.choose hA * Classical.choose hB : Kˣ) : K) •
            symplecticGram K := by
              conv_lhs => rw [Classical.choose_spec hB, smul_smul]
              rfl

theorem symplecticMultiplier_spec (A : symplecticSimilitudes K) :
    A.val.valᵀ * symplecticGram K * A.val.val =
      (symplecticMultiplier A : K) • symplecticGram K := Classical.choose_spec A.property

theorem symplecticMultiplier_kernel_iff (A : symplecticSimilitudes K) :
    A ∈ symplecticMultiplier.ker ↔
      A.val.valᵀ * symplecticGram K * A.val.val = symplecticGram K := by
  constructor
  · intro h
    rw [symplecticMultiplier_spec, (symplecticMultiplier.mem_ker.mp h)]
    simp
  · intro h
    apply symplecticMultiplier.mem_ker.mpr
    exact symplectic_multiplier_unique A.val _ 1 (symplecticMultiplier_spec A) (by simpa using h)

end CFSG.ComponentClassification.CatalogueBOrthogonalFive
