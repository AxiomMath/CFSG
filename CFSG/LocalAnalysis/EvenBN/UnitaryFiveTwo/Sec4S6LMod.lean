module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Lev
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSSeven

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

@[expose] def antiM : Matrix (Fin 2) (Fin 2) F4 := !![0, 1; 1, 0]

theorem det_antiM : antiM.det = 1 := by
  rw [antiM, Matrix.det_fin_two_of]
  decide

theorem isUnit_det_antiM : IsUnit antiM.det := by
  rw [det_antiM]
  exact isUnit_one

theorem barInvT_antiM : barInvT hF4 antiM = antiM := barInvT_eq (by
  rw [hF4_bar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiM, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero])

theorem levSU_antiM : levSU antiM isUnit_det_antiM = vSU := by
  refine ext_mat ?_
  ext i j
  rw [mat_levSU, det_antiM, map_one, div_one, CFSG.ClassicalGroups.UnitaryFlag.oddDiag,
    barInvT_antiM, mat_vSU]
  fin_cases i <;> fin_cases j <;>
    simp [yIdx, blk3, antiM, vMat, Matrix.fromBlocks]

@[expose] def antiSL : Matrix.SpecialLinearGroup (Fin 2) F4 := ⟨antiM, det_antiM⟩

theorem levSLHom_antiSL : levSLHom antiSL = vSU := by
  have : levSLHom antiSL = levSU antiM isUnit_det_antiM := rfl
  rw [this, levSU_antiM]

theorem vSU_mem_levSLHom_range : vSU ∈ levSLHom.range := ⟨antiSL, levSLHom_antiSL⟩

theorem X₂sub_le_levSLHom_range : X₂sub ≤ levSLHom.range := by
  intro g hg
  obtain ⟨a, ha⟩ := mem_X₂sub.1 hg
  refine ⟨CFSG.LocalAnalysis.ComponentInitial.sl2Upper F4 (bar a), ?_⟩
  rw [levSLHom_sl2Upper, bar_bar]
  exact ext_mat (by rw [mat_x₂SU, ha])

theorem K₂sub_eq_levSLHom_range : K₂sub = levSLHom.range := by
  apply le_antisymm
  · exact sup_le X₂sub_le_levSLHom_range (zpowers_le.2 vSU_mem_levSLHom_range)
  · rintro _ ⟨V, rfl⟩
    exact levSLHom_mem_K₂sub V

theorem levSLHom_injective : Function.Injective levSLHom :=
  levHom_injective.comp Matrix.SpecialLinearGroup.toGL_injective

@[expose] noncomputable def k2Equiv : Matrix.SpecialLinearGroup (Fin 2) F4 ≃* K₂sub :=
  (MonoidHom.ofInjective levSLHom_injective).trans (MulEquiv.subgroupCongr K₂sub_eq_levSLHom_range.symm)

theorem K₂sub_eq_sup_conj : K₂sub = X₂sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom := by
  apply le_antisymm
  · rw [K₂sub_eq_levSLHom_range]
    rintro _ ⟨V, rfl⟩
    have hgen : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F4)) ≤
        (X₂sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom).comap levSLHom := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := F4),
        Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show levSLHom (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F4 c) ∈
          X₂sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom
        rw [levSLHom_sl2Upper]
        exact mem_sup_left (x₂SU_mem _)
      · show levSLHom (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F4 c) ∈
          X₂sub ⊔ X₂sub.map (MulAut.conj vSU).toMonoidHom
        rw [levSLHom_sl2Lower]
        refine mem_sup_right ⟨x₂SU (bar c), x₂SU_mem _, ?_⟩
        show vSU * x₂SU (bar c) * vSU⁻¹ = vSU * x₂SU (bar c) * vSU
        rw [vSU_inv]
    exact hgen (Subgroup.mem_top V)
  · refine sup_le X₂sub_le_K₂sub ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem vSU_mem_K₂sub (X₂sub_le_K₂sub hx)) (inv_mem vSU_mem_K₂sub)

@[expose] def diagOmM : Matrix (Fin 2) (Fin 2) F4 := !![1, 0; 0, F4.ω]

theorem det_diagOmM : diagOmM.det = F4.ω := by
  rw [diagOmM, Matrix.det_fin_two_of]
  simp

theorem isUnit_det_diagOmM : IsUnit diagOmM.det := by
  rw [det_diagOmM]
  exact IsUnit.mk0 _ (by decide)

theorem barInvT_diagOmM : barInvT hF4 diagOmM = !![1, 0; 0, F4.ω] := barInvT_eq (by
  rw [hF4_bar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagOmM, Matrix.mul_apply, Fin.sum_univ_two, bar_apply] <;> decide)

theorem levSU_diagOmM : levSU diagOmM isUnit_det_diagOmM = e₁SU := by
  refine ext_mat ?_
  ext i j
  rw [mat_levSU, det_diagOmM, CFSG.ClassicalGroups.UnitaryFlag.oddDiag, barInvT_diagOmM, mat_e₁SU]
  fin_cases i <;> fin_cases j <;>
    simp [yIdx, blk3, diagOmM, e₁Mat, Matrix.diagonal, Matrix.fromBlocks, bar_apply] <;> decide

theorem e₁SU_mem_levHom_range : e₁SU ∈ levHom.range :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero diagOmM isUnit_det_diagOmM.ne_zero, by
    rw [levHom_apply]
    exact levSU_diagOmM⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
