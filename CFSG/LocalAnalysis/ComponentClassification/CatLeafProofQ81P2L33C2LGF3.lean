module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

@[expose] def torus3 (a : K) (ha : a ≠ 0) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![a, 1, a⁻¹], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp [ha]⟩

theorem coe_torus3 (a : K) (ha : a ≠ 0) :
    (torus3 a ha : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![a, 1, a⁻¹] := rfl

theorem torus3_inv (a : K) (ha : a ≠ 0) :
    (torus3 a ha)⁻¹ = torus3 a⁻¹ (inv_ne_zero ha) := by
  refine inv_eq_of_mul_eq_one_right ?_
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_torus3, coe_torus3, diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [ha]

@[expose] def antiW : GL (Fin 3) K :=
  ⟨(Equiv.swap (0 : Fin 3) 2).permMatrix K, (Equiv.swap (0 : Fin 3) 2).permMatrix K,
    by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one],
    by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one]⟩

theorem antiW_conj (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    ((antiW : GL (Fin 3) K) * M * ((antiW⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i j =
      M (Equiv.swap 0 2 i) (Equiv.swap 0 2 j) := by
  change ((Equiv.swap (0 : Fin 3) 2).permMatrix K * M * (Equiv.swap (0 : Fin 3) 2).permMatrix K)
    i j = _
  simp only [Matrix.mul_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  simp [Fin.sum_univ_three, Equiv.swap_apply_def]
  fin_cases i <;> fin_cases j <;> simp

theorem antiW_fix {σ : K ≃+* K} {g g' : SpecialLinearGroup (Fin 3) K} (hg' : g⁻¹ = g')
    (h : ∀ i j, σ ((g' : Matrix (Fin 3) (Fin 3) K) (Equiv.swap 0 2 j) (Equiv.swap 0 2 i)) =
      (g : Matrix (Fin 3) (Fin 3) K) i j) :
    (conjAut 3 K antiW * fieldAut 3 K σ * dualAut 3 K) (proj 3 K g) = proj 3 K g := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj]
  congr 1
  ext i j
  rw [coe_slConjugation, antiW_conj, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_transpose, hg',
    Matrix.transpose_apply]
  exact h i j

end CFSG.ComponentClassification.HarrisLit.L33.C2
