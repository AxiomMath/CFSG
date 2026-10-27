module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvBlock
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Orth3Mod
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification
open scoped MatrixGroups commutatorElement

section Hom

variable {F : Type} [Field F]

structure DiagAd (e : Fin 3 → F) (ρ : SL(2, F) →* SL(3, F)) : Prop where
  iso : ∀ S, (ρ S : Matrix (Fin 3) (Fin 3) F)ᵀ * Matrix.diagonal e * (ρ S : Matrix (Fin 3) (Fin 3) F) =
    Matrix.diagonal e
  irr : ∀ W : Submodule F (Fin 3 → F),
    (∀ S : SL(2, F), ∀ v ∈ W, (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
  comm : ∀ T : Matrix (Fin 3) (Fin 3) F,
    (∀ S : SL(2, F), T * (ρ S : Matrix (Fin 3) (Fin 3) F) = (ρ S : Matrix (Fin 3) (Fin 3) F) * T) →
      ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F)
  ker : ∀ S, ρ S = 1 → S = 1 ∨ S = -1

theorem cls3_diagonal_inv_mul {n : Type*} [Fintype n] [DecidableEq n] {e : n → F} (he : ∀ i, e i ≠ 0) :
    Matrix.diagonal (fun i => (e i)⁻¹) * Matrix.diagonal e = (1 : Matrix n n F) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (he i)

theorem cls3_diagonal_mul_inv {n : Type*} [Fintype n] [DecidableEq n] {e : n → F} (he : ∀ i, e i ≠ 0) :
    Matrix.diagonal e * Matrix.diagonal (fun i => (e i)⁻¹) = (1 : Matrix n n F) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (he i)

@[expose] def cls3Diag (e : Fin 3 → F) (he : ∀ i, e i ≠ 0) : GL (Fin 3) F :=
  ⟨Matrix.diagonal e, Matrix.diagonal fun i => (e i)⁻¹, cls3_diagonal_mul_inv he, cls3_diagonal_inv_mul he⟩

theorem exists_diagAd [Finite F] (hodd : Odd (Nat.card F)) (e : Fin 3 → F) (he : ∀ i, e i ≠ 0) :
    ∃ ρ : SL(2, F) →* SL(3, F), DiagAd e ρ := by
  have hR : ((cls3Diag e he : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ =
      (cls3Diag e he : GL (Fin 3) F) := by
    simp [cls3Diag, Matrix.diagonal_transpose]
  obtain ⟨ρ, hiso, hirr, hcomm, hker⟩ := exists_ad_hom3 hodd (cls3Diag e he) hR
  refine ⟨ρ, ⟨fun S => ?_, hirr, hcomm, hker⟩⟩
  have := (CatalogueBGraphForm.mem_isometryGroup 3 F (cls3Diag e he) _).1 (hiso S)
  simpa [cls3Diag] using this

@[expose] def cls3FixedVecs (ρ : SL(2, F) →* SL(3, F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ S : SL(2, F), (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  add_mem' {a b} ha hb S := by rw [Matrix.mulVec_add, ha S, hb S]
  zero_mem' S := Matrix.mulVec_zero _
  smul_mem' c v hv S := by rw [Matrix.mulVec_smul, hv S]

@[expose] def cls3Transv (F : Type) [Field F] : SL(2, F) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem DiagAd.fixed_vec {e : Fin 3 → F} {ρ : SL(2, F) →* SL(3, F)} (hρ : DiagAd e ρ)
    (h2 : (2 : F) ≠ 0) {v : Fin 3 → F} (hv : ∀ S : SL(2, F), (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    v = 0 := by
  rcases hρ.irr (cls3FixedVecs ρ) (fun S v hv => by
      show ∀ T : SL(2, F), (ρ T : Matrix (Fin 3) (Fin 3) F) *ᵥ ((ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ v
      rw [hv S]; exact hv) with h | h
  · have : v ∈ cls3FixedVecs ρ := hv
    rw [h] at this
    exact this
  · exfalso
    have hS0 : ρ (cls3Transv F) = 1 := by
      apply Subtype.ext
      ext i j
      have hj : (Pi.single j 1 : Fin 3 → F) ∈ cls3FixedVecs ρ := by rw [h]; exact Submodule.mem_top
      have := congrFun (hj (cls3Transv F)) i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this
    rcases hρ.ker _ hS0 with h1 | h1
    · have := congrArg (fun S : SL(2, F) => (S : Matrix (Fin 2) (Fin 2) F) 0 1) h1
      simp [cls3Transv] at this
    · have := congrArg (fun S : SL(2, F) => (S : Matrix (Fin 2) (Fin 2) F) 0 0) h1
      simp [cls3Transv] at this
      apply h2
      linear_combination this

theorem DiagAd.fixed_row {e : Fin 3 → F} {ρ : SL(2, F) →* SL(3, F)} (hρ : DiagAd e ρ)
    (he : ∀ i, e i ≠ 0) (h2 : (2 : F) ≠ 0) {r : Fin 3 → F}
    (hr : ∀ S : SL(2, F), r ᵥ* (ρ S : Matrix (Fin 3) (Fin 3) F) = r) : r = 0 := by
  have hDinv := cls3_diagonal_inv_mul he
  have hDinv' := cls3_diagonal_mul_inv he
  set u : Fin 3 → F := (Matrix.diagonal fun i => (e i)⁻¹) *ᵥ r with hu
  have hRu : Matrix.diagonal e *ᵥ u = r := by
    rw [hu, Matrix.mulVec_mulVec, hDinv', Matrix.one_mulVec]
  have hfix : ∀ S : SL(2, F), (ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u := by
    intro S
    have hT := hr S⁻¹
    have hmul : (ρ S⁻¹ : Matrix (Fin 3) (Fin 3) F) * (ρ S : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, inv_mul_cancel, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have key : (ρ S⁻¹ : Matrix (Fin 3) (Fin 3) F)ᵀ * Matrix.diagonal e =
        Matrix.diagonal e * (ρ S : Matrix (Fin 3) (Fin 3) F) := by
      calc (ρ S⁻¹ : Matrix (Fin 3) (Fin 3) F)ᵀ * Matrix.diagonal e
          = (ρ S⁻¹ : Matrix (Fin 3) (Fin 3) F)ᵀ * Matrix.diagonal e *
              ((ρ S⁻¹ : Matrix (Fin 3) (Fin 3) F) * (ρ S : Matrix (Fin 3) (Fin 3) F)) := by
            rw [hmul, Matrix.mul_one]
        _ = ((ρ S⁻¹ : Matrix (Fin 3) (Fin 3) F)ᵀ * Matrix.diagonal e *
              (ρ S⁻¹ : Matrix (Fin 3) (Fin 3) F)) * (ρ S : Matrix (Fin 3) (Fin 3) F) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.diagonal e * (ρ S : Matrix (Fin 3) (Fin 3) F) := by rw [hρ.iso S⁻¹]
    have h1 : Matrix.diagonal e *ᵥ ((ρ S : Matrix (Fin 3) (Fin 3) F) *ᵥ u) = Matrix.diagonal e *ᵥ u := by
      rw [Matrix.mulVec_mulVec, ← key, ← Matrix.mulVec_mulVec, hRu, Matrix.mulVec_transpose, hT]
    have h3 := congrArg (fun z => (Matrix.diagonal fun i => (e i)⁻¹) *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hDinv, Matrix.one_mul, Matrix.one_mulVec] at h3
    exact h3
  have hu0 := hρ.fixed_vec h2 hfix
  rw [← hRu, hu0, Matrix.mulVec_zero]

theorem cls3_eFirst_isometry (d : Fin 4 → F) {H : Matrix (Fin 3) (Fin 3) F}
    (hH : Hᵀ * Matrix.diagonal ![d 1, d 2, d 3] * H = Matrix.diagonal ![d 1, d 2, d 3]) :
    (eFirst H)ᵀ * Matrix.diagonal d * eFirst H = Matrix.diagonal d := by
  have e : ∀ i j, (Hᵀ * Matrix.diagonal ![d 1, d 2, d 3] * H) i j =
      Matrix.diagonal ![d 1, d 2, d 3] i j := fun i j => by rw [hH]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eFirst, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;>
    first | linear_combination e00 | linear_combination e01 | linear_combination e02 |
      linear_combination e10 | linear_combination e11 | linear_combination e12 |
      linear_combination e20 | linear_combination e21 | linear_combination e22

theorem cls3_eLast_isometry (d : Fin 4 → F) {H : Matrix (Fin 3) (Fin 3) F}
    (hH : Hᵀ * Matrix.diagonal ![d 0, d 1, d 2] * H = Matrix.diagonal ![d 0, d 1, d 2]) :
    (eLast H)ᵀ * Matrix.diagonal d * eLast H = Matrix.diagonal d := by
  have e : ∀ i j, (Hᵀ * Matrix.diagonal ![d 0, d 1, d 2] * H) i j =
      Matrix.diagonal ![d 0, d 1, d 2] i j := fun i j => by rw [hH]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eLast, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;>
    first | linear_combination e00 | linear_combination e01 | linear_combination e02 |
      linear_combination e10 | linear_combination e11 | linear_combination e12 |
      linear_combination e20 | linear_combination e21 | linear_combination e22

@[expose] def cls3IotaA (ρ : SL(2, F) →* SL(3, F)) : SL(2, F) →* SL(4, F) := eFirstHom.comp ρ

@[expose] def cls3IotaB (ρ : SL(2, F) →* SL(3, F)) : SL(2, F) →* SL(4, F) := eLastHom.comp ρ

theorem coe_cls3IotaA (ρ : SL(2, F) →* SL(3, F)) (S : SL(2, F)) :
    ((cls3IotaA ρ S : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = eFirst (ρ S : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem coe_cls3IotaB (ρ : SL(2, F) →* SL(3, F)) (S : SL(2, F)) :
    ((cls3IotaB ρ S : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = eLast (ρ S : Matrix (Fin 3) (Fin 3) F) :=
  rfl

theorem proj_cls3IotaA_mem {D : GL (Fin 4) F} {d : Fin 4 → F}
    (hD : ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d)
    {ρ : SL(2, F) →* SL(3, F)} (hρ : DiagAd ![d 1, d 2, d 3] ρ) (S : SL(2, F)) :
    proj 4 F (cls3IotaA ρ S) ∈ fixSub (conjAut 4 F D * dualAut 4 F) :=
  mem_fixSub.2 (conjAut_dualAut_proj_of_transpose_mul_mul D _
    (by rw [hD, coe_cls3IotaA]; exact cls3_eFirst_isometry d (hρ.iso S)))

theorem proj_cls3IotaB_mem {D : GL (Fin 4) F} {d : Fin 4 → F}
    (hD : ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal d)
    {ρ : SL(2, F) →* SL(3, F)} (hρ : DiagAd ![d 0, d 1, d 2] ρ) (S : SL(2, F)) :
    proj 4 F (cls3IotaB ρ S) ∈ fixSub (conjAut 4 F D * dualAut 4 F) :=
  mem_fixSub.2 (conjAut_dualAut_proj_of_transpose_mul_mul D _
    (by rw [hD, coe_cls3IotaB]; exact cls3_eLast_isometry d (hρ.iso S)))

end Hom

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
