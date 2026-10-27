module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4UMem

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

theorem embU_conj_mem (h : UnitaryFieldData p f K) {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
    {x : GL (Fin 4) K} (hx : x ∈ unitarySU p f K 4)
    (hcomm : (x : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![1, 1, ζ, ζ ^ 2] =
      Matrix.diagonal ![1, 1, ζ, ζ ^ 2] * (x : Matrix (Fin 4) (Fin 4) K))
    (A : unitarySU p f K 2) :
    ∃ B : unitarySU p f K 2, (embU h B : GL (Fin 4) K) =
      x * (embU h A : GL (Fin 4) K) * x⁻¹ := by
  have hζ1 : ζ ≠ 1 := by
    simpa using hζ.pow_ne_one_of_pos_of_lt (l := 1) one_ne_zero (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (l := 2) two_ne_zero (by norm_num)
  have hζζ : ζ ≠ ζ ^ 2 := by
    intro hz
    apply hζ1
    have hz0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
    have : ζ * ζ = ζ * 1 := by rw [mul_one, ← pow_two, ← hz]
    exact mul_left_cancel₀ hz0 this
  have hvdist : ∀ i j : Fin 4, ¬ (i.val < 2 ∧ j.val < 2) → i ≠ j →
      (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) i ≠ (![1, 1, ζ, ζ ^ 2] : Fin 4 → K) j := by
    intro i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hζ1, Ne.symm hζ2, Ne.symm hζζ]
  have hXY : (x : Matrix (Fin 4) (Fin 4) K) * ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      1 := Units.mul_inv x
  have hYX : ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K) =
      1 := Units.inv_mul x
  have hOx : OffBlock (x : Matrix (Fin 4) (Fin 4) K) :=
    offBlock_of_comm_diag _ _ hcomm hvdist
  have hcomm' : ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.diagonal ![1, 1, ζ, ζ ^ 2] = Matrix.diagonal ![1, 1, ζ, ζ ^ 2] *
        ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    calc ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![1, 1, ζ, ζ ^ 2]
        = ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![1, 1, ζ, ζ ^ 2] *
          ((x : Matrix (Fin 4) (Fin 4) K) * ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
          rw [hXY, Matrix.mul_one]
      _ = ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (Matrix.diagonal ![1, 1, ζ, ζ ^ 2] * (x : Matrix (Fin 4) (Fin 4) K)) *
          ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
          simp only [Matrix.mul_assoc]
      _ = ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((x : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![1, 1, ζ, ζ ^ 2]) *
          ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
          rw [← hcomm]
      _ = (((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K)) *
          Matrix.diagonal ![1, 1, ζ, ζ ^ 2] * ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal ![1, 1, ζ, ζ ^ 2] * ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
          rw [hYX, Matrix.one_mul]
  have hOy : OffBlock ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
    offBlock_of_comm_diag _ _ hcomm' hvdist
  have hblock : IsBlock ((x : Matrix (Fin 4) (Fin 4) K) *
      embM ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :=
    isBlock_conj hXY hYX hOx hOy (isBlock_embM ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
  have hg : x * (embU h A : GL (Fin 4) K) * x⁻¹ ∈ unitarySU p f K 4 :=
    mul_mem (mul_mem hx (embU h A).2) (inv_mem hx)
  have hgblock : IsBlock ((x * (embU h A : GL (Fin 4) K) * x⁻¹ : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) := by
    rw [Units.val_mul, Units.val_mul]
    exact hblock
  exact exists_embU_eq_of_isBlock h _ hg hgblock

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
