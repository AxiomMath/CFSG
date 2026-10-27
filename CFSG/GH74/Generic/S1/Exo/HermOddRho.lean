module

public import CFSG.GH74.Generic.S1.Exo.HermOddDefs

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module Matrix QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadMinus)
open scoped MatrixGroups

variable {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] (D : OddNormPlane K E)

@[expose] noncomputable def hermOddIsometry :
    (evenNormTailForm (-D.N) 1).IsometryEquiv (hermOddForm D) where
  toLinearEquiv := hermOddCoord D
  map_app' v := by
    simp [hermOddForm, QuadraticMap.comp_apply]

theorem hermOddForm_coord (v : ((Fin 1 → K) × (Fin 1 → K)) × E) :
    hermOddForm D (hermOddCoord D v) = v.1.1 0 * v.1.2 0 - D.N v.2 := by
  have := (hermOddIsometry D).map_app v
  rw [show (hermOddIsometry D) v = hermOddCoord D v from rfl] at this
  rw [this, evenNormTailForm_apply]
  simp [sub_eq_add_neg]

omit [Finite K] in
theorem det_hermOddMat (a b : K) (z : E) :
    (hermOddMat D.σ a b z).det = algebraMap K E a * algebraMap K E b - z * D.σ z := by
  simp [hermOddMat, Matrix.det_fin_two]

theorem algebraMap_hermOddForm (X : hermOddSpace D.σ) :
    algebraMap K E (hermOddForm D X) = (X : Matrix (Fin 2) (Fin 2) E).det := by
  obtain ⟨v, rfl⟩ := (hermOddCoord D).surjective X
  rw [hermOddForm_coord, coe_hermOddCoord, det_hermOddMat, map_sub, map_mul, D.algebraMap_N]

theorem exists_isometry_hermOddForm_quadMinus :
    ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty ((hermOddForm D).IsometryEquiv (quadMinus 2 K b c)) := by
  obtain ⟨b, c, hirr, ⟨θ⟩⟩ := exists_binForm_isometryEquiv D.finrank_eq (-D.N)
    (fun z hz => D.eq_zero_of_N_eq_zero (by simpa using hz))
  exact ⟨b, c, hirr, ⟨(hermOddIsometry D).symm.trans (evenNormTailIsometry θ 1)⟩⟩

theorem finrank_hermOddSpace : finrank K (hermOddSpace D.σ) = 4 := by
  have := D.moduleFinite
  rw [← (hermOddCoord D).finrank_eq]
  simp [Module.finrank_prod, D.finrank_eq]

theorem nondegenerate_hermOddForm : (polarBilin (hermOddForm D)).Nondegenerate := by
  obtain ⟨b, c, hirr, ⟨ι⟩⟩ := exists_isometry_hermOddForm_quadMinus D
  exact nondegenerate_polarBilin_of_isometryEquiv ι.symm
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)

theorem not_isPlusType_hermOddForm : ¬ IsPlusType (hermOddForm D) := by
  obtain ⟨b, c, hirr, ⟨ι⟩⟩ := exists_isometry_hermOddForm_quadMinus D
  exact fun h => not_isPlusType_quadMinus (by norm_num) hirr ((isPlusType_congr ι).1 h)

theorem hermOddRho_mem (g : SL(2, E)) :
    hermOddRho D g ∈ TauCeti.QuadraticMap.orthogonalGroup (hermOddForm D) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro X
  apply (algebraMap K E).injective
  rw [algebraMap_hermOddForm, algebraMap_hermOddForm, coe_hermOddRho, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose]
  have h1 : (g.1.map D.σ).det = D.σ g.1.det := by
    simpa using (AlgHom.map_det D.σ.toAlgHom g.1).symm
  rw [h1, g.2, map_one, one_mul, mul_one]

end CFSG.GH74.Generic.S1.Exo
