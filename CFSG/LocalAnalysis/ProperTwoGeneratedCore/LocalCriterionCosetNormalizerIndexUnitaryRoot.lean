module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Background.Huppert.II.theorem_10_12

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External
open scoped Matrix

universe u

theorem hermitian_square_one_mem_center
    {K : Type u} [Field K] [CharP K 2] {n : ℕ} (J : HermitianForm n K)
    (z : hermitianUnipotentCoord J) (hz : z ^ 2 = 1) :
    z ∈ Subgroup.center (hermitianUnipotentCoord J) := by
  have hsecond := congrArg (fun a : hermitianUnipotentCoord J => a.1.2) hz
  rw [pow_two] at hsecond
  change z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 = 0 at hsecond
  rw [CharTwo.add_self_eq_zero, zero_sub, neg_eq_zero] at hsecond
  have hfirst : z.1.1 = 0 := by
    rcases mul_eq_zero.mp hsecond with h | h
    · exact h
    · exact J.conj.injective (by simpa only [map_zero] using h)
  apply Subgroup.mem_center_iff.mpr
  intro w
  change hermitianUnipotentMul J w z = hermitianUnipotentMul J z w
  apply Subtype.ext
  apply Prod.ext
  · simp only [hermitianUnipotentMul, hfirst, zero_add, add_zero]
  · simp only [hermitianUnipotentMul, hfirst, map_zero, zero_mul, mul_zero, sub_zero]
    exact add_comm _ _

theorem hermitian_root_range_eq_of_coordinates
    {K : Type u} [Field K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (coord : hermitianUnipotentCoord J ≃ R)
    (hcoord : ∀ z : hermitianUnipotentCoord J,
      ∃ M : GL (Fin 3) K,
        (M : Matrix (Fin 3) (Fin 3) K) =
          !![1, z.1.1, z.1.2; 0, 1, -J.conj z.1.1; 0, 0, 1] ∧
        (((coord z : R) : ProjectiveSpecialUnitaryMatrixGroup J) :
          Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk M) :
    (hermitianUnipotentPSU J hJ).range = R := by
  have hmatch (z : hermitianUnipotentCoord J) :
      (coord z : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianUnipotentPSU J hJ z := by
    obtain ⟨M, hM, hproj⟩ := hcoord z
    have hMeq : M = hermitianUnipotentGL J z := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [hM, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq]
    apply Subtype.ext
    simpa only [hermitianUnipotentPSU_val, hMeq] using hproj
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rw [← hmatch]
    exact (coord z).property
  · intro hx
    obtain ⟨z, hz⟩ := coord.surjective ⟨x, hx⟩
    exact ⟨z, (hmatch z).symm.trans (congrArg Subtype.val hz)⟩

theorem hermitian_root_square_one_mem_center_of_coordinates
    {K : Type u} [Field K] [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (coord : hermitianUnipotentCoord J ≃ R)
    (hcoord : ∀ z : hermitianUnipotentCoord J,
      ∃ M : GL (Fin 3) K,
        (M : Matrix (Fin 3) (Fin 3) K) =
          !![1, z.1.1, z.1.2; 0, 1, -J.conj z.1.1; 0, 0, 1] ∧
        (((coord z : R) : ProjectiveSpecialUnitaryMatrixGroup J) :
          Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk M)
    (r : R) (hr : r ^ 2 = 1) : r ∈ Subgroup.center R := by
  let f := hermitianUnipotentPSU J hJ
  have hrange := hermitian_root_range_eq_of_coordinates J hJ R coord hcoord
  let e : hermitianUnipotentCoord J ≃* R :=
    (MulEquiv.ofBijective f.rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ), f.rangeRestrict_surjective⟩).trans
      (MulEquiv.subgroupCongr hrange)
  have hpre : (e.symm r) ^ 2 = 1 := by
    simpa only [map_pow, map_one] using congrArg e.symm hr
  rw [← Subgroup.map_center_eq e]
  exact Subgroup.mem_map.mpr
    ⟨e.symm r, hermitian_square_one_mem_center J _ hpre, e.apply_symm_apply r⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
