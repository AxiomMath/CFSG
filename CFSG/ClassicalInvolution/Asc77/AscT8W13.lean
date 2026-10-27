module

public import CFSG.ClassicalInvolution.Asc77.AscT8W12
public import CFSG.ClassicalInvolution.Asc77.AscT8V11
public import CFSG.ClassicalInvolution.Asc77.AscT8W11
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Inner

variable {F : Type} [Field F]

theorem conj_comm_of_eigen {G Mm Mi Δ B : Matrix (Fin 4) (Fin 4) F} (hGM : G * Mm = Mm * Δ)
    (hMMi : Mm * Mi = 1) (hMiM : Mi * Mm = 1) (hΔB : Δ * B = B * Δ) :
    G * (Mm * B * Mi) = (Mm * B * Mi) * G := by
  have hMiG : Mi * G = Δ * Mi := by
    calc Mi * G = Mi * G * (Mm * Mi) := by rw [hMMi, Matrix.mul_one]
      _ = (Mi * (G * Mm)) * Mi := by simp only [Matrix.mul_assoc]
      _ = (Mi * (Mm * Δ)) * Mi := by rw [hGM]
      _ = Δ * Mi := by rw [← Matrix.mul_assoc Mi Mm, hMiM, Matrix.one_mul]
  calc G * (Mm * B * Mi) = (G * Mm) * B * Mi := by simp only [Matrix.mul_assoc]
    _ = Mm * (Δ * B) * Mi := by rw [hGM]; simp only [Matrix.mul_assoc]
    _ = Mm * (B * Δ) * Mi := by rw [hΔB]
    _ = Mm * B * (Δ * Mi) := by simp only [Matrix.mul_assoc]
    _ = (Mm * B * Mi) * G := by rw [← hMiG]; simp only [Matrix.mul_assoc]

theorem delta1_comm_block (a : F) (A : Matrix (Fin 2) (Fin 2) F) :
    (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, -a] : Matrix (Fin 4) (Fin 4) F) *
        CFSG.ClassicalInvolution.Phan.blockMat 4 0 A =
      CFSG.ClassicalInvolution.Phan.blockMat 4 0 A *
        !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, -a] ∧
    (!![a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, -a] : Matrix (Fin 4) (Fin 4) F) *
        CFSG.ClassicalInvolution.Phan.blockMat 4 1 A =
      CFSG.ClassicalInvolution.Phan.blockMat 4 1 A *
        !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, -a] := by
  rw [blockMat_four_zero, blockMat_four_one]
  constructor <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring)

theorem delta2_comm_block (a : F) (A : Matrix (Fin 2) (Fin 2) F) :
    (!![-a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, a] : Matrix (Fin 4) (Fin 4) F) *
        CFSG.ClassicalInvolution.Phan.blockMat 4 1 A =
      CFSG.ClassicalInvolution.Phan.blockMat 4 1 A *
        !![-a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, a] ∧
    (!![-a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, a] : Matrix (Fin 4) (Fin 4) F) *
        CFSG.ClassicalInvolution.Phan.blockMat 4 2 A =
      CFSG.ClassicalInvolution.Phan.blockMat 4 2 A *
        !![-a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, a] := by
  rw [blockMat_four_one, blockMat_four_two]
  constructor <;> (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring)

theorem sl4_inner_case (h2 : (2 : F) ≠ 0) (α : SL(4, F) →* SL(4, F))
    (G Gi : Matrix (Fin 4) (Fin 4) F) (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    (hdet : G.det ≠ 0) (φ : F ≃+* F)
    (hmat : ∀ x : SL(4, F), ((α x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      G * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4) F) * Gi)
    (hα2 : ∀ x, α (α x) = x)
    (hα0 : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, α r = r) :
    (∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, α r = r) ∨
    ∃ Mgl : GL (Fin 4) F,
      (∀ i : Fin 3, i ≠ 2 → ∀ s ∈ (blockSL2 F 3 i).range,
        α (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s) =
          CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s) ∧
      (∀ i : Fin 3, i ≠ 0 → ∀ s ∈ (blockSL2 F 3 i).range,
        α (negTwo F *
          CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s *
            (negTwo F)⁻¹) =
          CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F Mgl s) := by
  classical
  have key : ∀ x : SL(4, F), α x = x →
      (x : Matrix (Fin 4) (Fin 4) F) * G = G * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4) F) := by
    intro x hx
    have h := hmat x
    rw [hx] at h
    calc (x : Matrix (Fin 4) (Fin 4) F) * G
        = (G * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4) F) * Gi) * G := by rw [← h]
      _ = G * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4) F) := by
          rw [Matrix.mul_assoc, hGiG, Matrix.mul_one]
  have hr01 : ∀ t : F, E01 t * G = G * E01 (φ t) := fun t => by
    have := key (u01 t) (hα0 _ (u01_mem t))
    simpa [RingEquiv.mapMatrix_apply, map_E01, u01] using this
  have hr10 : ∀ t : F, E10 t * G = G * E10 (φ t) := fun t => by
    have := key (u10 t) (hα0 _ (u10_mem t))
    simpa [RingEquiv.mapMatrix_apply, map_E10, u10] using this
  obtain ⟨hφ, a, ha, hG⟩ := shape_block0_zero φ G hdet hr01 hr10
  obtain ⟨h22, h23, h32, h33, hGeq⟩ : ∃ h22 h23 h32 h33 : F,
      G = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] := ⟨_, _, _, _, hG⟩
  subst hφ
  have hsq : ∀ x : SL(4, F), (G * G) * (x : Matrix (Fin 4) (Fin 4) F) =
      (x : Matrix (Fin 4) (Fin 4) F) * (G * G) := by
    intro x
    have h1 := hmat (α x)
    have h2' := hmat x
    have h3 : ((α (α x) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = G * (G * x * Gi) * Gi := by
      rw [h1, h2', mapMatrix_refl', mapMatrix_refl']
    rw [hα2 x] at h3
    calc (G * G) * (x : Matrix (Fin 4) (Fin 4) F)
        = (G * (G * (x : Matrix (Fin 4) (Fin 4) F) * Gi) * Gi) * (G * G) := by
          calc (G * G) * (x : Matrix (Fin 4) (Fin 4) F)
              = (G * G) * (x : Matrix (Fin 4) (Fin 4) F) * (Gi * (Gi * G) * G) := by
                rw [hGiG, Matrix.mul_one, hGiG, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]
      _ = (x : Matrix (Fin 4) (Fin 4) F) * (G * G) := by rw [← h3]
  obtain ⟨c, hc⟩ := sq_scalar_of_commute (G * G) hsq
  have hGG : G * G = !![a * a, 0, 0, 0; 0, a * a, 0, 0; 0, 0, h22 * h22 + h23 * h32,
      h22 * h23 + h23 * h33; 0, 0, h32 * h22 + h33 * h32, h32 * h23 + h33 * h33] := by
    rw [hGeq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have hca : c = a * a := by
    have := congrFun (congrFun hc 0) 0
    rw [hGG] at this
    simpa using this
  have hH2 : (!![h22, h23; h32, h33] : Matrix (Fin 2) (Fin 2) F) * !![h22, h23; h32, h33] =
      (a * a) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have e22 := congrFun (congrFun hc 2) 2
    have e23 := congrFun (congrFun hc 2) 3
    have e32 := congrFun (congrFun hc 3) 2
    have e33 := congrFun (congrFun hc 3) 3
    rw [hGG] at e22 e23 e32 e33
    simp [hca] at e22 e23 e32 e33
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination e22 | linear_combination -e22 | linear_combination e23
        | linear_combination -e23 | linear_combination e32 | linear_combination -e32
        | linear_combination e33 | linear_combination -e33
  by_cases hscal : ∃ c' : F, (!![h22, h23; h32, h33] : Matrix (Fin 2) (Fin 2) F) =
      c' • (1 : Matrix (Fin 2) (Fin 2) F)
  ·
    left
    obtain ⟨c', hc'⟩ := hscal
    have e22 := congrFun (congrFun hc' 0) 0
    have e23 := congrFun (congrFun hc' 0) 1
    have e32 := congrFun (congrFun hc' 1) 0
    have e33 := congrFun (congrFun hc' 1) 1
    simp at e22 e23 e32 e33
    rintro r ⟨A, rfl⟩
    apply Subtype.ext
    rw [hmat, mapMatrix_refl']
    apply alpha_fix_of_comm hGGi
    rw [coe_blockSL, blockMat_four_two, hGeq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, e22, e23, e32, e33] <;> ring
  ·
    right
    obtain ⟨p, q, r, s, hdetpq, e1, e2, e3, e4⟩ := exists_eigenbasis h2 ha _ hH2 hscal
    simp at e1 e2 e3 e4
    set Mm : Matrix (Fin 4) (Fin 4) F := !![0, 1, 0, 0; 0, 0, 1, 0; p, 0, 0, r; q, 0, 0, s]
      with hMm
    have hMdet : Mm.det = p * s - q * r := by
      simp [hMm, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
      ring
    let Mgl : GL (Fin 4) F :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Mm (by rw [hMdet]; exact hdetpq)
    have hMgl : (Mgl : Matrix (Fin 4) (Fin 4) F) = Mm := rfl
    set Mi : Matrix (Fin 4) (Fin 4) F := ((Mgl⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      with hMi
    have hMMi : Mm * Mi = 1 := by rw [← hMgl, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hMiM : Mi * Mm = 1 := by rw [← hMgl, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hGM : G * Mm = Mm * !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, -a] := by
      rw [hGeq, hMm]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
      · linear_combination e1
      · linear_combination e3
      · linear_combination e2
      · linear_combination e4
    have hGYM : (G * (negTwo F : Matrix (Fin 4) (Fin 4) F)) * Mm =
        Mm * !![-a, 0, 0, 0; 0, a, 0, 0; 0, 0, a, 0; 0, 0, 0, a] := by
      rw [hGeq, hMm, coe_negTwo]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
      · linear_combination -e1
      · linear_combination -e3
      · linear_combination -e2
      · linear_combination -e4
    have hYY : negTwo F * negTwo F = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_negTwo]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
    have hYinv : (negTwo F)⁻¹ = negTwo F := inv_eq_of_mul_eq_one_right hYY
    refine ⟨Mgl, ?_, ?_⟩
    · intro i hi s hs
      obtain ⟨A, rfl⟩ := hs
      apply Subtype.ext
      rw [hmat, mapMatrix_refl', coe_slConjugation]
      apply alpha_fix_of_comm hGGi
      refine conj_comm_of_eigen hGM hMMi hMiM ?_
      fin_cases i
      · exact (delta1_comm_block a A).1
      · exact (delta1_comm_block a A).2
      · exact absurd rfl hi
    · intro i hi s hs
      obtain ⟨A, rfl⟩ := hs
      apply Subtype.ext
      rw [hmat, mapMatrix_refl', hYinv, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation]
      have hcomm : (G * (negTwo F : Matrix (Fin 4) (Fin 4) F)) *
          (Mm * ((blockSL2 F 3 i A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Mi) =
          (Mm * ((blockSL2 F 3 i A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Mi) *
            (G * (negTwo F : Matrix (Fin 4) (Fin 4) F)) := by
        refine conj_comm_of_eigen hGYM hMMi hMiM ?_
        fin_cases i
        · exact absurd rfl hi
        · exact (delta2_comm_block a A).1
        · exact (delta2_comm_block a A).2
      have hYGi : (negTwo F : Matrix (Fin 4) (Fin 4) F) * (negTwo F : Matrix (Fin 4) (Fin 4) F) =
          1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, hYY]
        rfl
      calc G * ((negTwo F : Matrix (Fin 4) (Fin 4) F) *
            (Mm * ((blockSL2 F 3 i A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Mi) *
              (negTwo F : Matrix (Fin 4) (Fin 4) F)) * Gi
          = (G * (negTwo F : Matrix (Fin 4) (Fin 4) F)) *
              (Mm * ((blockSL2 F 3 i A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Mi) *
                ((negTwo F : Matrix (Fin 4) (Fin 4) F) * Gi) := by
            simp only [Matrix.mul_assoc]
        _ = (Mm * ((blockSL2 F 3 i A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Mi) *
              (G * (negTwo F : Matrix (Fin 4) (Fin 4) F)) *
                ((negTwo F : Matrix (Fin 4) (Fin 4) F) * Gi) := by rw [hcomm]
        _ = Mm * ((blockSL2 F 3 i A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Mi := by
            calc (Mm * ((blockSL2 F 3 i A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Mi) *
                  (G * (negTwo F : Matrix (Fin 4) (Fin 4) F)) *
                    ((negTwo F : Matrix (Fin 4) (Fin 4) F) * Gi)
                = (Mm * ((blockSL2 F 3 i A : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * Mi) *
                    (G * ((negTwo F : Matrix (Fin 4) (Fin 4) F) *
                      (negTwo F : Matrix (Fin 4) (Fin 4) F)) * Gi) := by
                  simp only [Matrix.mul_assoc]
              _ = _ := by rw [hYGi, Matrix.mul_one, hGGi, Matrix.mul_one]

theorem alpha_fix_of_rel {G Gi X Y : Matrix (Fin 4) (Fin 4) F} (hGGi : G * Gi = 1)
    (h : G * X = Y * G) : G * X * Gi = Y := by
  rw [h, Matrix.mul_assoc, hGGi, Matrix.mul_one]

theorem sl4_graph_case (h2 : (2 : F) ≠ 0) (α : SL(4, F) →* SL(4, F))
    (G Gi : Matrix (Fin 4) (Fin 4) F) (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    (hdet : G.det ≠ 0) (φ : F ≃+* F)
    (hmat : ∀ x : SL(4, F), ((α x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      G * φ.mapMatrix (((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ * Gi)
    (hα2 : ∀ x, α (α x) = x)
    (hα0 : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, α r = r) :
    ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, α r = r := by
  classical
  have key : ∀ x : SL(4, F), α x = x →
      (x : Matrix (Fin 4) (Fin 4) F) * G =
        G * φ.mapMatrix (((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ := by
    intro x hx
    have h := hmat x
    rw [hx] at h
    calc (x : Matrix (Fin 4) (Fin 4) F) * G
        = (G * φ.mapMatrix (((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ * Gi) * G := by
          rw [← h]
      _ = G * φ.mapMatrix (((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ := by
          rw [Matrix.mul_assoc, hGiG, Matrix.mul_one]
  have hr01 : ∀ t : F, E01 t * G = G * E10 (-φ t) := fun t => by
    have := key (u01 t) (hα0 _ (u01_mem t))
    have h1 : (((u01 t)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ = E10 (-t) := by
      rw [← Matrix.SpecialLinearGroup.coe_transpose]
      exact coe_inv_transpose_u01 t
    rw [h1] at this
    simpa [RingEquiv.mapMatrix_apply, map_E10, u01] using this
  have hr10 : ∀ t : F, E10 t * G = G * E01 (-φ t) := fun t => by
    have := key (u10 t) (hα0 _ (u10_mem t))
    have h1 : (((u10 t)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ = E01 (-t) := by
      rw [← Matrix.SpecialLinearGroup.coe_transpose]
      exact coe_inv_transpose_u10 t
    rw [h1] at this
    simpa [RingEquiv.mapMatrix_apply, map_E01, u10] using this
  obtain ⟨hφ, m, hm, hG⟩ := shape_block0_one φ G hdet hr01 hr10
  obtain ⟨h22, h23, h32, h33, hGeq⟩ : ∃ h22 h23 h32 h33 : F,
      G = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, h22, h23; 0, 0, h32, h33] := ⟨_, _, _, _, hG⟩
  subst hφ
  have hΛ : ∀ x : SL(4, F), (G * Giᵀ) * (x : Matrix (Fin 4) (Fin 4) F) =
      (x : Matrix (Fin 4) (Fin 4) F) * (G * Giᵀ) := by
    intro x
    have h1 := hmat (α x)
    have h2' := hmat (α x)⁻¹
    have hinv : ((α x)⁻¹ : SL(4, F)) = α (x⁻¹) := (map_inv α x).symm
    have h3 : (((α x)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        G * (x : Matrix (Fin 4) (Fin 4) F)ᵀ * Gi := by
      rw [hinv, hmat (x⁻¹), inv_inv, mapMatrix_refl']
    have h4 : ((α (α x) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        G * (Giᵀ * (x : Matrix (Fin 4) (Fin 4) F) * Gᵀ) * Gi := by
      rw [hmat (α x), mapMatrix_refl', h3, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
    rw [hα2 x] at h4
    have hGTGiT : Gᵀ * Giᵀ = 1 := by
      rw [← Matrix.transpose_mul, hGiG, Matrix.transpose_one]
    have hΛ'Λ : (Gᵀ * Gi) * (G * Giᵀ) = 1 := by
      calc (Gᵀ * Gi) * (G * Giᵀ) = Gᵀ * (Gi * G) * Giᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hGiG, Matrix.mul_one, hGTGiT]
    have h4' : (x : Matrix (Fin 4) (Fin 4) F) =
        (G * Giᵀ) * (x : Matrix (Fin 4) (Fin 4) F) * (Gᵀ * Gi) := by
      calc (x : Matrix (Fin 4) (Fin 4) F)
          = G * (Giᵀ * (x : Matrix (Fin 4) (Fin 4) F) * Gᵀ) * Gi := h4
        _ = (G * Giᵀ) * (x : Matrix (Fin 4) (Fin 4) F) * (Gᵀ * Gi) := by
          simp only [Matrix.mul_assoc]
    calc (G * Giᵀ) * (x : Matrix (Fin 4) (Fin 4) F)
        = ((G * Giᵀ) * (x : Matrix (Fin 4) (Fin 4) F) * (Gᵀ * Gi)) * (G * Giᵀ) := by
          rw [Matrix.mul_assoc _ (Gᵀ * Gi), hΛ'Λ, Matrix.mul_one]
      _ = (x : Matrix (Fin 4) (Fin 4) F) * (G * Giᵀ) := by rw [← h4']
  obtain ⟨c, hc⟩ := sq_scalar_of_commute _ hΛ
  have hGc : G = c • Gᵀ := by
    have hGiTGT : Giᵀ * Gᵀ = 1 := by
      rw [← Matrix.transpose_mul, hGGi, Matrix.transpose_one]
    calc G = G * Giᵀ * Gᵀ := by rw [Matrix.mul_assoc, hGiTGT, Matrix.mul_one]
      _ = c • Gᵀ := by
          rw [← hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
            Matrix.one_mul]
  have e01 := congrFun (congrFun hGc 0) 1
  have e22 := congrFun (congrFun hGc 2) 2
  have e33 := congrFun (congrFun hGc 3) 3
  have e23 := congrFun (congrFun hGc 2) 3
  rw [hGeq] at e01 e22 e33 e23
  simp at e01 e22 e33 e23
  have hc1 : c = -1 := by
    have h : m * (1 + c) = 0 := by linear_combination e01
    have := (mul_eq_zero.mp h).resolve_left hm
    linear_combination this
  subst hc1
  have h22z : h22 = 0 := by
    have : (2 : F) * h22 = 0 := by linear_combination e22
    exact (mul_eq_zero.mp this).resolve_left h2
  have h33z : h33 = 0 := by
    have : (2 : F) * h33 = 0 := by linear_combination e33
    exact (mul_eq_zero.mp this).resolve_left h2
  have h32v : h32 = -h23 := by linear_combination e23
  rintro r ⟨A, rfl⟩
  apply Subtype.ext
  rw [hmat, mapMatrix_refl']
  apply alpha_fix_of_rel hGGi
  have hinv : (((blockSL F 4 2 2 (by norm_num) A)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      CFSG.ClassicalInvolution.Phan.blockMat 4 2 (Matrix.adjugate (A : Matrix (Fin 2) (Fin 2) F)) :=
    by
      rw [← map_inv, coe_blockSL, Matrix.SpecialLinearGroup.coe_inv]
  rw [hinv, Matrix.adjugate_fin_two, coe_blockSL, blockMat_four_two, blockMat_four_two, hGeq,
    h22z, h33z, h32v]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

end Inner

section Main

variable {p e : ℕ} [Fact p.Prime]


theorem sl4_gen_std (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {X : Type} [Group X]
    (ψ : SL(4, GaloisField p e) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center SL(4, GaloisField p e))
    (hSperf : Group.IsPerfect SL(4, GaloisField p e))
    (hperf0 : (blockSL (GaloisField p e) 4 2 0 (by norm_num)).range ≤
      ⁅(blockSL (GaloisField p e) 4 2 0 (by norm_num)).range,
        (blockSL (GaloisField p e) 4 2 0 (by norm_num)).range⁆)
    (σ : MulAut X) (hσ2 : ∀ x, σ (σ x) = x)
    (h0 : ∀ r ∈ (blockSL (GaloisField p e) 4 2 0 (by norm_num)).range, σ (ψ r) = ψ r)
    (hnt : ∃ r ∈ (blockSL (GaloisField p e) 4 2 2 (by norm_num)).range, σ (ψ r) ≠ ψ r) :
    Subgroup.closure ({g | σ g = g} ∪
      {g | σ (ψ (negTwo (GaloisField p e)) * g * (ψ (negTwo (GaloisField p e)))⁻¹) = g}) =
        ⊤ := by
  classical
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  obtain ⟨α, g, φ, ε, hlift, hmat⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification hp2 hq (n := 4)
      (by norm_num) X ψ hψ hker σ
  have hα0 : ∀ r ∈ (blockSL (GaloisField p e) 4 2 0 (by norm_num)).range, α r = r :=
    CFSG.ClassicalInvolution.Asc77.T8V.eq_of_central_ratio α hperf0 (fun r hr => hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, h0 r hr, mul_inv_cancel]))
  have hα2 : ∀ x, α (α x) = x := by
    have := CFSG.ClassicalInvolution.Asc77.T8V.eq_of_central_ratio (α.comp α) (P := ⊤)
      (CFSG.ClassicalInvolution.Asc77.T8V.top_le_commutator_of_perfect hSperf) (fun x _ =>
        hker (by
          rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.comp_apply, hlift, hlift, hσ2,
            mul_inv_cancel]))
    intro x
    simpa using this x (Subgroup.mem_top x)
  have hblock2 : (∀ r ∈ (blockSL (GaloisField p e) 4 2 2 (by norm_num)).range, α r = r) →
      False := by
    intro h
    obtain ⟨r, hr, hne⟩ := hnt
    exact hne (by rw [← hlift, h r hr])
  have hGGi : (g : Matrix (Fin 4) (Fin 4) (GaloisField p e)) *
      ((g⁻¹ : GL (Fin 4) (GaloisField p e)) : Matrix (Fin 4) (Fin 4) (GaloisField p e)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : ((g⁻¹ : GL (Fin 4) (GaloisField p e)) : Matrix (Fin 4) (Fin 4) (GaloisField p e)) *
      (g : Matrix (Fin 4) (Fin 4) (GaloisField p e)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : (g : Matrix (Fin 4) (Fin 4) (GaloisField p e)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  cases ε
  · have hmat' : ∀ x : SL(4, GaloisField p e),
        ((α x : SL(4, GaloisField p e)) : Matrix (Fin 4) (Fin 4) (GaloisField p e)) =
          (g : Matrix (Fin 4) (Fin 4) (GaloisField p e)) * φ.mapMatrix (x : Matrix (Fin 4) (Fin 4)
            (GaloisField p e)) * ((g⁻¹ : GL (Fin 4) (GaloisField p e)) :
              Matrix (Fin 4) (Fin 4) (GaloisField p e)) := fun x => by simpa using hmat x
    rcases sl4_inner_case h2 α _ _ hGGi hGiG hdet φ hmat' hα2 hα0 with h | ⟨Mgl, h₁, h₂⟩
    · exact absurd h hblock2
    · exact closure_fix_eq_top ψ hψ σ α hlift (negTwo _) Mgl h₁ h₂
  · have hmat' : ∀ x : SL(4, GaloisField p e),
        ((α x : SL(4, GaloisField p e)) : Matrix (Fin 4) (Fin 4) (GaloisField p e)) =
          (g : Matrix (Fin 4) (Fin 4) (GaloisField p e)) * φ.mapMatrix
            (((x⁻¹ : SL(4, GaloisField p e)) : Matrix (Fin 4) (Fin 4) (GaloisField p e)))ᵀ *
              ((g⁻¹ : GL (Fin 4) (GaloisField p e)) :
                Matrix (Fin 4) (Fin 4) (GaloisField p e)) := fun x => by simpa using hmat x
    exact absurd (sl4_graph_case h2 α _ _ hGGi hGiG hdet φ hmat' hα2 hα0) hblock2

end Main

end CFSG.ClassicalInvolution.Asc77.T8W
