module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open Matrix

@[expose] noncomputable def kerCardCyclo3 {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) : ℕ :=
  Nat.card {v : ι → F // M.mulVec (M.mulVec v) + M.mulVec v + v = 0}

private def zmodHom (F : Type) [Field F] [CharP F 2] : ZMod 2 →+* F :=
  ZMod.castHom (dvd_refl 2) F

private def matHom (F : Type) [Field F] [CharP F 2] :
    Matrix (Fin 4) (Fin 4) (ZMod 2) →+* Matrix (Fin 4) (Fin 4) F :=
  (zmodHom F).mapMatrix

private def M2 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1]

private def M2sq : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]

private def D2 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 0]

private def Rho2 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1]

private theorem M2_mul_M2sq : M2 * M2sq = 1 := by decide
private theorem M2sq_mul_M2 : M2sq * M2 = 1 := by decide
private theorem M2_cube : M2 ^ 3 = 1 := by decide
private theorem M2_cyclo : M2 * M2 + M2 + 1 = D2 := by decide
private theorem M2_mem : M2ᵀ * minorJ (ZMod 2) * M2 = minorJ (ZMod 2) := by decide
private theorem minorMap_M2 : minorMap M2 = Rho2 := by decide
private theorem Rho2_cyclo : Rho2 * Rho2 + Rho2 + 1 = 0 := by decide

private theorem matHom_apply {F : Type} [Field F] [CharP F 2]
    (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    matHom F M = M.map (zmodHom F) := rfl

private theorem MF_transpose {F : Type} [Field F] [CharP F 2] :
    (matHom F M2)ᵀ = matHom F (M2ᵀ) := by
  change (M2.map (zmodHom F))ᵀ = (M2ᵀ).map (zmodHom F)
  exact Matrix.transpose_map

private theorem MF_mem {F : Type} [Field F] [CharP F 2] :
    (matHom F M2)ᵀ * minorJ F * matHom F M2 = minorJ F := by
  rw [MF_transpose, ← minorJ_map (zmodHom F),
    ← matHom_apply (F := F) (minorJ (ZMod 2)), ← map_mul, ← map_mul, M2_mem]

private theorem MF_cyclo {F : Type} [Field F] [CharP F 2] :
    matHom F M2 * matHom F M2 + matHom F M2 + 1 = matHom F D2 := by
  rw [← map_mul (matHom F), ← map_add (matHom F), ← map_one (matHom F),
    ← map_add (matHom F), M2_cyclo]

private theorem MF_cube {F : Type} [Field F] [CharP F 2] :
    (matHom F M2) ^ 3 = 1 := by
  rw [← map_pow, M2_cube, map_one (matHom F)]

private theorem minorMap_map {F : Type} [Field F] [CharP F 2]
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    minorMap (matHom F g) = matHom F (minorMap g) := by
  change minorMap (g.map (zmodHom F)) = (minorMap g).map (zmodHom F)
  ext A B
  simp only [minorMap_apply, Matrix.map_apply, map_sub, map_mul]

private theorem minorMap_MF {F : Type} [Field F] [CharP F 2] :
    minorMap (matHom F M2) = matHom F Rho2 := by
  rw [minorMap_map, minorMap_M2]

private theorem Rho_cyclo {F : Type} [Field F] [CharP F 2] :
    matHom F Rho2 * matHom F Rho2 + matHom F Rho2 + 1 = 0 := by
  rw [← map_mul (matHom F), ← map_add (matHom F), ← map_one (matHom F),
    ← map_add (matHom F), Rho2_cyclo, map_zero (matHom F)]

private theorem mulVec_quad {F : Type} [Field F] (M : Matrix (Fin 4) (Fin 4) F)
    (v : Fin 4 → F) :
    M.mulVec (M.mulVec v) + M.mulVec v + v = (M * M + M + 1).mulVec v := by
  rw [Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]

private theorem D_mulVec_eq_zero_iff {F : Type} [Field F] [CharP F 2] (v : Fin 4 → F) :
    (matHom F D2).mulVec v = 0 ↔ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := congrFun h 1
      simpa [matHom_apply, Matrix.map_apply, Matrix.mulVec_apply, dotProduct,
        Matrix.row_apply, Fin.sum_univ_four, D2] using h1
    · have h2 := congrFun h 2
      simpa [matHom_apply, Matrix.map_apply, Matrix.mulVec_apply, dotProduct,
        Matrix.row_apply, Fin.sum_univ_four, D2] using h2
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;>
      simp [matHom_apply, Matrix.map_apply, Matrix.mulVec_apply, dotProduct,
        Matrix.row_apply, Fin.sum_univ_four, D2, h1, h2]

private noncomputable def coordsEquiv {F : Type} [Field F] :
    {v : Fin 4 → F // v 1 = 0 ∧ v 2 = 0} ≃ F × F where
  toFun v := (v.1 0, v.1 3)
  invFun p := ⟨![p.1, 0, 0, p.2], by constructor <;> simp⟩
  left_inv v := by
    ext i
    fin_cases i <;> simp [v.2.1, v.2.2]
  right_inv p := by
    ext <;> simp

private noncomputable def x0Unit (F : Type) [Field F] [CharP F 2] : GL (Fin 4) F :=
  ⟨matHom F M2, matHom F M2sq,
    by rw [← map_mul, M2_mul_M2sq, map_one],
    by rw [← map_mul, M2sq_mul_M2, map_one]⟩

private noncomputable def x0 (F : Type) [Field F] [Finite F] [CharP F 2] : antiSp F :=
  ⟨x0Unit F, mem_antiSp.mpr (MF_mem (F := F))⟩

private theorem x0_cube {F : Type} [Field F] [Finite F] [CharP F 2] :
    x0 F ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change (matHom F M2) ^ 3 = 1
  exact MF_cube (F := F)

private theorem x0_rho {F : Type} [Field F] [Finite F] [CharP F 2] :
    minorAut F (minorAut F (x0 F)) = x0 F := by
  have h1 : minorAut F (minorAut F (x0 F)) = frobHom F (x0 F) := by
    rw [show minorAut F (minorAut F (x0 F)) = minorHom F (minorHom F (x0 F)) from rfl,
      minorHom_minorHom]
  rw [h1]
  apply antiSp_ext
  rw [glMat_frobHom]
  change (matHom F M2).map (fun x => x ^ 2) = matHom F M2
  ext i j
  rw [Matrix.map_apply, matHom_apply, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp [M2]

private theorem x0_ker {F : Type} [Field F] [Finite F] [CharP F 2] :
    kerCardCyclo3 (glMat (x0 F : GL (Fin 4) F)) = Nat.card F ^ 2 := by
  show Nat.card {v : Fin 4 → F //
    (matHom F M2).mulVec ((matHom F M2).mulVec v) + (matHom F M2).mulVec v + v = 0} =
      Nat.card F ^ 2
  have he : {v : Fin 4 → F //
      (matHom F M2).mulVec ((matHom F M2).mulVec v) + (matHom F M2).mulVec v + v = 0} ≃
        F × F :=
    (Equiv.subtypeEquiv (Equiv.refl _) (fun v => by
      rw [mulVec_quad, MF_cyclo]
      exact D_mulVec_eq_zero_iff v)).trans coordsEquiv
  rw [Nat.card_congr he, Nat.card_prod]
  ring

private theorem x0_ker_rho {F : Type} [Field F] [Finite F] [CharP F 2] :
    kerCardCyclo3 (glMat ((minorAut F (x0 F) : antiSp F) : GL (Fin 4) F)) =
      Nat.card F ^ 4 := by
  have hN : glMat ((minorAut F (x0 F) : antiSp F) : GL (Fin 4) F) = matHom F Rho2 := by
    rw [glMat_minorAut]
    show minorMap (matHom F M2) = matHom F Rho2
    rw [minorMap_MF]
  rw [hN]
  show Nat.card {v : Fin 4 → F //
    (matHom F Rho2).mulVec ((matHom F Rho2).mulVec v) + (matHom F Rho2).mulVec v + v = 0} =
      Nat.card F ^ 4
  have hpred : ∀ v : Fin 4 → F,
      (matHom F Rho2).mulVec ((matHom F Rho2).mulVec v) + (matHom F Rho2).mulVec v + v = 0 := by
    intro v
    rw [mulVec_quad, Rho_cyclo, Matrix.zero_mulVec]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hpred), Nat.card_fun,
    show Nat.card (Fin 4) = 4 by simp [Nat.card_eq_fintype_card]]

theorem exists_order_three_kerCardCyclo3 {F : Type} [Field F] [Finite F] [CharP F 2] :
    ∃ x₀ : antiSp F, x₀ ^ 3 = 1 ∧ minorAut F (minorAut F x₀) = x₀ ∧
      kerCardCyclo3 (glMat (x₀ : GL (Fin 4) F)) = Nat.card F ^ 2 ∧
      kerCardCyclo3 (glMat ((minorAut F x₀ : antiSp F) : GL (Fin 4) F)) = Nat.card F ^ 4 := by
  refine ⟨x0 F, x0_cube (F := F), x0_rho (F := F), ?_, ?_⟩
  · exact x0_ker (F := F)
  · exact x0_ker_rho (F := F)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
