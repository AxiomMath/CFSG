module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4YSplit
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

@[expose] def lowM (c : F4) : Matrix (Fin 2) (Fin 2) F4 := !![1, 0; c, 1]

theorem det_lowM (c : F4) : (lowM c).det = 1 := by
  rw [lowM, Matrix.det_fin_two_of]
  simp

theorem isUnit_det_lowM (c : F4) : IsUnit (lowM c).det := by
  rw [det_lowM]
  exact isUnit_one

theorem barInvT_lowM (c : F4) : barInvT hF4 (lowM c) = !![1, bar c; 0, 1] := barInvT_eq (by
  rw [hF4_bar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowM, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero])

theorem levSU_lowM (c : F4) :
    levSU (lowM c) (isUnit_det_lowM c) = vSU * x₂SU (bar c) * vSU := by
  have hdet : (lowM c).det = 1 := det_lowM c
  refine ext_mat ?_
  ext i j
  rw [mat_levSU, hdet, map_one, div_one, CFSG.ClassicalGroups.UnitaryFlag.oddDiag,
    barInvT_lowM, mat_mul, mat_mul, mat_vSU, mat_x₂SU]
  fin_cases i <;> fin_cases j <;>
    simp [yIdx, blk3, lowM, vMat, x₂Mat, Matrix.mul_apply, Fin.sum_univ_five,
      Matrix.fromBlocks, bar_bar]

@[expose] noncomputable def levSLHom : Matrix.SpecialLinearGroup (Fin 2) F4 →* SU52 :=
  levHom.comp Matrix.SpecialLinearGroup.toGL

theorem levSLHom_sl2Upper (c : F4) :
    levSLHom (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F4 c) = x₂SU (bar c) :=
  levSU_unip c

theorem levSLHom_sl2Lower (c : F4) :
    levSLHom (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F4 c) = vSU * x₂SU (bar c) * vSU :=
  levSU_lowM c

theorem X₂sub_le_K₂sub : X₂sub ≤ K₂sub := by
  rw [K₂sub]
  exact le_sup_left

theorem vSU_mem_K₂sub : vSU ∈ K₂sub := by
  rw [K₂sub]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers vSU)

theorem levSLHom_mem_K₂sub (V : Matrix.SpecialLinearGroup (Fin 2) F4) : levSLHom V ∈ K₂sub := by
  have hgen : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F4)) ≤ K₂sub.comap levSLHom := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := F4),
      Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show levSLHom _ ∈ K₂sub
      rw [levSLHom_sl2Upper]
      exact X₂sub_le_K₂sub (x₂SU_mem _)
    · show levSLHom _ ∈ K₂sub
      rw [levSLHom_sl2Lower]
      exact mul_mem (mul_mem vSU_mem_K₂sub (X₂sub_le_K₂sub (x₂SU_mem _))) vSU_mem_K₂sub
  exact hgen (Subgroup.mem_top V)

theorem isUnit_det_smul_one {c : F4} (hc : c ≠ 0) :
    IsUnit (c • (1 : Matrix (Fin 2) (Fin 2) F4)).det := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  exact (IsUnit.mk0 c hc).pow 2

theorem F4_unit_cases : ∀ c : F4, c ≠ 0 → c = 1 ∨ c = F4.ω ∨ c = F4.ω * F4.ω := by
  decide

theorem levSU_of_eq_one (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det) (h : A = 1) :
    levSU A hA = 1 := by
  subst h
  exact levSU_one _

theorem levSU_of_eq_omega (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det)
    (h : A = F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)) : levSU A hA = e₂SU := by
  subst h
  exact levSU_omega _

theorem levSU_of_eq_omega_sq (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det)
    (h : A = (F4.ω * F4.ω) • (1 : Matrix (Fin 2) (Fin 2) F4)) :
    levSU A hA = e₂SU * e₂SU := by
  subst h
  have hω : IsUnit (F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)).det :=
    isUnit_det_smul_one (by decide)
  have hsq : (F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)) * (F4.ω • 1) =
      (F4.ω * F4.ω) • (1 : Matrix (Fin 2) (Fin 2) F4) := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have hAB : IsUnit ((F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)) * (F4.ω • 1)).det := by
    rw [hsq]
    exact hA
  calc levSU ((F4.ω * F4.ω) • (1 : Matrix (Fin 2) (Fin 2) F4)) hA
      = levSU ((F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)) * (F4.ω • 1)) hAB := by
        congr 1
        exact hsq.symm
    _ = levSU (F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)) hω *
          levSU (F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)) hω :=
        levSU_mul _ _ hω hω hAB
    _ = e₂SU * e₂SU := by rw [levSU_omega hω]

theorem levSU_scalar_mem (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det) {c : F4}
    (hc : c ≠ 0) (h : A = c • (1 : Matrix (Fin 2) (Fin 2) F4)) :
    levSU A hA ∈ zpowers e₂SU := by
  rcases F4_unit_cases c hc with rfl | rfl | rfl
  · rw [levSU_of_eq_one A hA (by rw [h, one_smul])]
    exact one_mem _
  · rw [levSU_of_eq_omega A hA h]
    exact Subgroup.mem_zpowers _
  · rw [levSU_of_eq_omega_sq A hA h]
    exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem levHom_range_le : levHom.range ≤ zpowers e₂SU ⊔ K₂sub := by
  rintro _ ⟨U, rfl⟩
  rw [levHom_apply]
  set M : Matrix (Fin 2) (Fin 2) F4 := (U : Matrix (Fin 2) (Fin 2) F4) with hM
  have hMu : IsUnit M.det := Matrix.isUnits_det_units U
  have hd0 : M.det ≠ 0 := hMu.ne_zero
  set s : F4 := M.det ^ 2 with hs
  have hs0 : s ≠ 0 := pow_ne_zero 2 hd0
  have hss : s * s = M.det := by
    rw [hs, ← sq, F4.sq_sq]
  have hdetV : (s⁻¹ • M).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hss]
    calc s⁻¹ ^ 2 * (s * s) = (s⁻¹ * s) * (s⁻¹ * s) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hs0, one_mul]
  have hdecomp : (s • (1 : Matrix (Fin 2) (Fin 2) F4)) * (s⁻¹ • M) = M := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  have h1 : IsUnit (s • (1 : Matrix (Fin 2) (Fin 2) F4)).det := isUnit_det_smul_one hs0
  have h2 : IsUnit (s⁻¹ • M).det := by
    rw [hdetV]
    exact isUnit_one
  have h3 : IsUnit ((s • (1 : Matrix (Fin 2) (Fin 2) F4)) * (s⁻¹ • M)).det := by
    rw [hdecomp]
    exact hMu
  have key : levSU M hMu =
      levSU (s • (1 : Matrix (Fin 2) (Fin 2) F4)) h1 * levSU (s⁻¹ • M) h2 := by
    rw [← levSU_mul _ _ h1 h2 h3]
    congr 1
    exact hdecomp.symm
  rw [key]
  exact mul_mem (Subgroup.mem_sup_left (levSU_scalar_mem _ h1 hs0 rfl))
    (Subgroup.mem_sup_right (levSLHom_mem_K₂sub ⟨s⁻¹ • M, hdetV⟩))

theorem K₂sub_le_K₃sub : K₂sub ≤ K₃sub := by
  rw [K₂sub, K₃sub]
  refine sup_le ?_ le_sup_right
  exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))

theorem Data.Lev_le_zpowers_sup_K₃ {G : Type} [Group G] (d : Data G) :
    d.Lev ≤ zpowers d.e₂ ⊔ d.K₃ := by
  have hm : levHom.range ≤ zpowers e₂SU ⊔ K₃sub :=
    levHom_range_le.trans (sup_le_sup_left K₂sub_le_K₃sub _)
  have hz : d.pull (zpowers e₂SU) = zpowers d.e₂ := MonoidHom.map_zpowers d.ι e₂SU
  calc d.Lev = d.pull levHom.range := rfl
    _ ≤ d.pull (zpowers e₂SU ⊔ K₃sub) := d.pull_mono hm
    _ = d.pull (zpowers e₂SU) ⊔ d.pull K₃sub := d.pull_sup _ _
    _ = zpowers d.e₂ ⊔ d.K₃ := by
        rw [hz]
        rfl

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
