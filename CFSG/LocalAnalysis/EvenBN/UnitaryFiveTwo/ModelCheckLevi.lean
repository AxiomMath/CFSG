module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckC0
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

theorem levD_mul (A B : Matrix (Fin 2) (Fin 2) F4) :
    hF4.bar (A * B).det / (A * B).det = hF4.bar A.det / A.det * (hF4.bar B.det / B.det) := by
  rw [Matrix.det_mul, map_mul, mul_div_mul_comm]

theorem levSU_mul (A B : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det) (hB : IsUnit B.det)
    (hAB : IsUnit (A * B).det) : levSU (A * B) hAB = levSU A hA * levSU B hB := by
  refine ρ.injective (CFSG.RankThree.PartOne.U5K.Hyp.mat_injective ?_)
  rw [map_mul, levSU, levSU, levSU, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, CFSG.RankThree.PartOne.U5K.Hyp.mat_mul,
    CFSG.RankThree.PartOne.U5K.Hyp.mat_lev, CFSG.RankThree.PartOne.U5K.Hyp.mat_lev,
    CFSG.RankThree.PartOne.U5K.Hyp.mat_lev, CFSG.RankThree.PartOne.U5K.Hyp.oddDiag_mul,
    levD_mul]

theorem levSU_one (h1 : IsUnit (1 : Matrix (Fin 2) (Fin 2) F4).det) : levSU 1 h1 = 1 := by
  refine ρ.injective (CFSG.RankThree.PartOne.U5K.Hyp.mat_injective ?_)
  rw [levSU, MulEquiv.apply_symm_apply, map_one, CFSG.RankThree.PartOne.U5K.Hyp.mat_lev,
    CFSG.RankThree.PartOne.U5K.Hyp.mat_one, Matrix.det_one, map_one, div_one,
    CFSG.RankThree.PartOne.U5K.Hyp.oddDiag_one]

@[expose] noncomputable def levHom : GL (Fin 2) F4 →* SU52 where
  toFun U := levSU (U : Matrix (Fin 2) (Fin 2) F4) (Matrix.isUnits_det_units U)
  map_one' := levSU_one _
  map_mul' _ _ := levSU_mul _ _ _ _ _

theorem levHom_apply (U : GL (Fin 2) F4) :
    levHom U = levSU (U : Matrix (Fin 2) (Fin 2) F4) (Matrix.isUnits_det_units U) := rfl

theorem levHom_injective : Function.Injective levHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro U hU
  rw [MonoidHom.mem_ker, levHom_apply] at hU
  have e := congrArg (fun g => CFSG.RankThree.PartOne.U5K.Hyp.mat (ρ g)) hU
  simp only [levSU, MulEquiv.apply_symm_apply, map_one, CFSG.RankThree.PartOne.U5K.Hyp.mat_lev,
    CFSG.RankThree.PartOne.U5K.Hyp.mat_one] at e
  refine mem_bot.2 (Matrix.GeneralLinearGroup.ext fun i j => ?_)
  have := congrFun (congrFun e (.inl i)) (.inl j)
  rw [CFSG.ClassicalGroups.UnitaryFlag.oddDiag, blk3_inl_inl] at this
  rw [this, Matrix.GeneralLinearGroup.coe_one]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

theorem card_GL_two_F4 : Nat.card (GL (Fin 2) F4) = 180 := by
  rw [Matrix.card_GL_field, F4.card]
  decide

theorem card_levHom_range : Nat.card levHom.range = 180 := by
  rw [← card_GL_two_F4]
  exact Nat.card_congr (MonoidHom.ofInjective levHom_injective).toEquiv.symm

theorem mat_levSU (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det) (i j : Fin 5) :
    mat (levSU A hA) i j =
      CFSG.ClassicalGroups.UnitaryFlag.oddDiag hF4 A (hF4.bar A.det / A.det) (yIdx i) (yIdx j) := by
  rw [← mat_ρ_apply, levSU, MulEquiv.apply_symm_apply, CFSG.RankThree.PartOne.U5K.Hyp.mat_lev]

theorem barInvT_eq {A B : Matrix (Fin 2) (Fin 2) F4} (h : (A.map hF4.bar)ᵀ * B = 1) :
    barInvT hF4 A = B := by
  have h' : B * (A.map hF4.bar)ᵀ = 1 := mul_eq_one_comm.1 h
  have hinv : (A.map hF4.bar)⁻¹ = Bᵀ := Matrix.inv_eq_right_inv (by
    have := congrArg Matrix.transpose h'
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this)
  rw [barInvT, hinv, Matrix.transpose_transpose]

@[expose] def unipM (b : F4) : Matrix (Fin 2) (Fin 2) F4 := !![1, b; 0, 1]

theorem isUnit_det_unipM (b : F4) : IsUnit (unipM b).det := by
  rw [unipM, Matrix.det_fin_two_of]
  simp

theorem levSU_unip (b : F4) : levSU (unipM b) (isUnit_det_unipM b) = x₂SU (bar b) := by
  have hdet : (unipM b).det = 1 := by
    rw [unipM, Matrix.det_fin_two_of]
    simp
  have hB : barInvT hF4 (unipM b) = !![1, 0; bar b, 1] := barInvT_eq (by
    rw [hF4_bar]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipM, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero])
  refine ext_mat ?_
  ext i j
  rw [mat_levSU, hdet, map_one, div_one, CFSG.ClassicalGroups.UnitaryFlag.oddDiag, hB, mat_x₂SU]
  fin_cases i <;> fin_cases j <;> simp [yIdx, blk3, unipM, x₂Mat, Matrix.fromBlocks, bar_bar]

theorem levSU_omega (h : IsUnit (F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)).det) :
    levSU (F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)) h = e₂SU := by
  have hdet : (F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)).det = F4.ω * F4.ω := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
    ring
  have hd : hF4.bar (F4.ω * F4.ω) / (F4.ω * F4.ω) = bar F4.ω := by
    rw [hF4_bar, bar_apply, bar_apply]
    decide
  have hB : barInvT hF4 (F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)) =
      F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4) := barInvT_eq (by
    rw [hF4_bar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, bar_apply] <;> decide)
  refine ext_mat ?_
  ext i j
  rw [mat_levSU, hdet, hd, CFSG.ClassicalGroups.UnitaryFlag.oddDiag, hB, mat_e₂SU]
  fin_cases i <;> fin_cases j <;> simp [yIdx, blk3, e₂Mat, Matrix.fromBlocks, Matrix.diagonal]

theorem levSU_comm_e₂SU (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det) :
    levSU A hA * e₂SU = e₂SU * levSU A hA := by
  have hω : IsUnit (F4.ω • (1 : Matrix (Fin 2) (Fin 2) F4)).det := by
    rw [Matrix.det_smul, Matrix.det_one]
    exact (IsUnit.mk0 _ (by decide)).pow _ |>.mul isUnit_one
  have e : A * (F4.ω • 1) = (F4.ω • 1) * A := by rw [Matrix.mul_smul, Matrix.smul_mul]; simp
  rw [← levSU_omega hω, ← levSU_mul _ _ hA hω (by rw [Matrix.det_mul]; exact hA.mul hω),
    ← levSU_mul _ _ hω hA (by rw [Matrix.det_mul]; exact hω.mul hA)]
  congr 1

theorem X₂sub_le_levHom_range : X₂sub ≤ levHom.range := by
  intro g hg
  obtain ⟨a, ha⟩ := mem_X₂sub.1 hg
  have hU : IsUnit (unipM (bar a)).det := isUnit_det_unipM _
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (unipM (bar a)) hU.ne_zero, ?_⟩
  rw [levHom_apply]
  change levSU (unipM (bar a)) _ = g
  rw [levSU_unip, bar_bar]
  exact ext_mat (by rw [mat_x₂SU, ha])

@[expose] def conjX₁ (c : F4) : SU52 := x₂SU c * x₁SU 0 1 zero_one_rel * (x₂SU c)⁻¹

theorem mat_conjX₁ (c : F4) : mat (conjX₁ c) = x₂Mat c * x₁Mat 0 1 * x₂Mat c := by
  rw [conjX₁, mat_mul, mat_mul, mat_inv_of_x₂ (mat_x₂SU c), mat_x₂SU, mat_x₁SU]

theorem x₄_eq_conjX₁ :
    x₄SU 0 1 zero_one_rel = conjX₁ 1 * conjX₁ F4.ω * conjX₁ (F4.ω + 1) * conjX₁ 0 := by
  refine ext_mat ?_
  rw [mat_mul, mat_mul, mat_mul, mat_conjX₁, mat_conjX₁, mat_conjX₁, mat_conjX₁, mat_x₄SU]
  decide +kernel

theorem x₃_eq_conjX₁ (c : F4) (hc : c ≠ 0) :
    x₃SU c = conjX₁ 0 * conjX₁ c * x₄SU 0 1 zero_one_rel := by
  refine ext_mat ?_
  rw [mat_mul, mat_mul, mat_conjX₁, mat_conjX₁, mat_x₄SU, mat_x₃SU]
  revert c
  decide +kernel

theorem x₁_eq_conjX₁ : x₁SU 0 1 zero_one_rel = conjX₁ 0 := by
  refine ext_mat ?_
  rw [mat_conjX₁, mat_x₁SU]
  decide +kernel

theorem Fsub_le_closure_conj_x₁ :
    Fsub ≤ closure (Set.range conjX₁) := by
  have hmem : ∀ c, conjX₁ c ∈ closure (Set.range conjX₁) := fun c => subset_closure ⟨c, rfl⟩
  have h4 : x₄SU 0 1 zero_one_rel ∈ closure (Set.range conjX₁) := by
    rw [x₄_eq_conjX₁]
    exact mul_mem (mul_mem (mul_mem (hmem _) (hmem _)) (hmem _)) (hmem _)
  rw [← closure_genFSU, closure_le]
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · change x₁SU 0 1 zero_one_rel ∈ _
    rw [x₁_eq_conjX₁]
    exact hmem 0
  · change x₃SU 1 ∈ _
    rw [x₃_eq_conjX₁ 1 one_ne_zero]
    exact mul_mem (mul_mem (hmem _) (hmem _)) h4
  · change x₃SU F4.ω ∈ _
    rw [x₃_eq_conjX₁ F4.ω (by decide)]
    exact mul_mem (mul_mem (hmem _) (hmem _)) h4
  · exact h4

theorem conj_x₂_x₁_ne_one :
    x₂SU 1 * x₁SU 0 1 zero_one_rel * (x₂SU 1)⁻¹ * (x₁SU 0 1 zero_one_rel)⁻¹ ≠ 1 := by
  intro e
  have h1 : mat (x₁SU 0 1 zero_one_rel)⁻¹ = x₁Mat 0 1 :=
    mat_inv_eq (by rw [mat_x₁SU]; decide +kernel)
  have := congrArg mat e
  rw [mat_mul, mat_mul, mat_mul, h1, mat_inv_of_x₂ (mat_x₂SU 1), mat_x₂SU, mat_x₁SU,
    mat_one] at this
  revert this
  decide +kernel

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
