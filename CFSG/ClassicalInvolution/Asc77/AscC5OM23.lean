module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM22
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

section Calculus

theorem fieldSp_mul_conjSp' (σ : F ≃+* F) (A : gsp 2 F) :
    fieldSp 2 F σ * conjSp 2 F A = conjSp 2 F (gspFieldMap σ A) * fieldSp 2 F σ := by
  refine MulEquiv.ext fun g => ?_
  apply Subtype.ext
  change glFieldEquiv (Fin 2 ⊕ Fin 2) σ ((A : GL (Fin 2 ⊕ Fin 2) F) * g *
      (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹) =
    glFieldEquiv (Fin 2 ⊕ Fin 2) σ A * glFieldEquiv (Fin 2 ⊕ Fin 2) σ g *
      (glFieldEquiv (Fin 2 ⊕ Fin 2) σ A)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem fieldSp_comm [Finite F] (σ τ : F ≃+* F) :
    fieldSp 2 F σ * fieldSp 2 F τ = fieldSp 2 F τ * fieldSp 2 F σ := by
  rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm F σ τ]

theorem comm_conjSp_fieldSp [Finite F] (M N : gsp 2 F) (σ τ : F ≃+* F) :
    conjSp 2 F M * fieldSp 2 F σ * (conjSp 2 F N * fieldSp 2 F τ) *
        (conjSp 2 F M * fieldSp 2 F σ)⁻¹ * (conjSp 2 F N * fieldSp 2 F τ)⁻¹ =
      conjSp 2 F (M * gspFieldMap σ N * gspFieldMap τ M⁻¹ * N⁻¹) := by
  have h1 := fieldSp_mul_conjSp' σ N
  have h2 := fieldSp_mul_conjSp' τ M⁻¹
  have h3 := fieldSp_comm (F := F) σ τ
  calc conjSp 2 F M * fieldSp 2 F σ * (conjSp 2 F N * fieldSp 2 F τ) *
        (conjSp 2 F M * fieldSp 2 F σ)⁻¹ * (conjSp 2 F N * fieldSp 2 F τ)⁻¹ =
      conjSp 2 F M * (fieldSp 2 F σ * conjSp 2 F N) * fieldSp 2 F τ * (fieldSp 2 F σ)⁻¹ *
        conjSp 2 F M⁻¹ * (fieldSp 2 F τ)⁻¹ * conjSp 2 F N⁻¹ := by
        simp only [mul_inv_rev, map_inv]
        group
    _ = conjSp 2 F M * conjSp 2 F (gspFieldMap σ N) * (fieldSp 2 F σ * fieldSp 2 F τ) *
        (fieldSp 2 F σ)⁻¹ * conjSp 2 F M⁻¹ * (fieldSp 2 F τ)⁻¹ * conjSp 2 F N⁻¹ := by
        rw [h1]
        group
    _ = conjSp 2 F M * conjSp 2 F (gspFieldMap σ N) * (fieldSp 2 F τ * conjSp 2 F M⁻¹) *
        (fieldSp 2 F τ)⁻¹ * conjSp 2 F N⁻¹ := by
        rw [h3]
        group
    _ = conjSp 2 F (M * gspFieldMap σ N * gspFieldMap τ M⁻¹ * N⁻¹) := by
        rw [h2, map_mul, map_mul, map_mul]
        group

theorem gm_mul (M N : gsp 2 F) : gm (M * N) = gm M * gm N := rfl

theorem gm_gspFieldMap (σ : F ≃+* F) (M : gsp 2 F) : gm (gspFieldMap σ M) = (gm M).map σ := rfl

theorem gm_inv (M : gsp 2 F) : gm M⁻¹ = (gm M)⁻¹ := by
  rw [gm, gm, Subgroup.coe_inv, Matrix.coe_units_inv]

end Calculus

section Lift

variable {S Y₁ Y₂ : Type} [Group S] [Group Y₁] [Group Y₂]

theorem symm_apply_of_lift (ψ₁ : S →* Y₁) (ψ₂ : S →* Y₂) (γ : Y₁ ≃* Y₂) (α : MulAut S)
    (h : ∀ x, γ (ψ₁ x) = ψ₂ (α x)) (x : S) : γ.symm (ψ₂ x) = ψ₁ (α⁻¹ x) := by
  rw [MulEquiv.symm_apply_eq, h]
  congr 1
  simp

theorem comm_apply_of_lift (ψ : S →* Y₁) (γ δ : Y₁ ≃* Y₁) (α β : MulAut S)
    (hγ : ∀ x, γ (ψ x) = ψ (α x)) (hδ : ∀ x, δ (ψ x) = ψ (β x)) (x : S) :
    γ (δ (γ.symm (δ.symm (ψ x)))) = ψ ((α * β * α⁻¹ * β⁻¹) x) := by
  rw [symm_apply_of_lift ψ ψ δ β hδ, symm_apply_of_lift ψ ψ γ α hγ, hδ, hγ]
  rfl

theorem comm_apply_of_lift_swap (ψ₁ : S →* Y₁) (ψ₂ : S →* Y₂) (ψ' : Y₂ ≃* Y₁) (δ₁ : Y₁ ≃* Y₁)
    (δ₂ : Y₂ ≃* Y₂) (α' β₁ β₂ : MulAut S) (hψ' : ∀ x, ψ' (ψ₂ x) = ψ₁ (α' x))
    (hδ₁ : ∀ x, δ₁ (ψ₁ x) = ψ₁ (β₁ x)) (hδ₂ : ∀ x, δ₂ (ψ₂ x) = ψ₂ (β₂ x)) (x : S) :
    ψ' (δ₂ (ψ'.symm (δ₁.symm (ψ₁ x)))) = ψ₁ ((α' * β₂ * α'⁻¹ * β₁⁻¹) x) := by
  rw [symm_apply_of_lift ψ₁ ψ₁ δ₁ β₁ hδ₁, symm_apply_of_lift ψ₂ ψ₁ ψ' α' hψ', hδ₂, hψ']
  rfl

end Lift

section Blocks

theorem bd_inv {h : Fin 2 → Matrix (Fin 2) (Fin 2) F} (hh : ∀ k, (h k).det ≠ 0) :
    (bd h)⁻¹ = bd (fun k => (h k)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [bd_mul, ← bd_one]
  congr 1
  funext k
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hh k))

theorem mat_conjSp_fieldSp' (M : gsp 2 F) (σ : F ≃+* F) (x : StatedSp 2 F) :
    mat 2 F (conjSp 2 F M (fieldSp 2 F σ x)) = gm M * (mat 2 F x).map σ * (gm M)⁻¹ := by
  rw [mat_apply, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp, Matrix.coe_units_inv]
  rfl

theorem mat_conjSp_fieldSp_longBlock (M : gsp 2 F) {g : Fin 2 → Matrix (Fin 2) (Fin 2) F}
    (hM : gm M = bd g) (σ : F ≃+* F) (k : Fin 2) (b : SL(2, F)) :
    mat 2 F (conjSp 2 F M (fieldSp 2 F σ (longBlock F 2 k b))) =
      bd (fun k' => if k' = k then g k * (b : Matrix (Fin 2) (Fin 2) F).map σ * (g k)⁻¹
        else 1) := by
  have hdet : ∀ k, (g k).det ≠ 0 := fun k => by
    rw [det_eq_mu_of_gm_eq_bd M hM k]
    exact Units.ne_zero _
  rw [mat_conjSp_fieldSp', hM, bd_inv hdet, mat_longBlock_eq_bd, bd_map, bd_mul, bd_mul]
  congr 1
  funext k'
  split_ifs with h
  · subst h
    rfl
  · rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.mul_one]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet k'))

theorem conjSp_fieldSp_longBlock (M : gsp 2 F) {g : Fin 2 → Matrix (Fin 2) (Fin 2) F}
    (hM : gm M = bd g) (σ : F ≃+* F) (k : Fin 2) (b c : SL(2, F))
    (hc : (c : Matrix (Fin 2) (Fin 2) F) = g k * (b : Matrix (Fin 2) (Fin 2) F).map σ * (g k)⁻¹) :
    conjSp 2 F M (fieldSp 2 F σ (longBlock F 2 k b)) = longBlock F 2 k c := by
  apply mat_injective
  rw [mat_conjSp_fieldSp_longBlock M hM σ k b, mat_longBlock_eq_bd, hc]

theorem conjSp_eq_conj_of_bd (C : gsp 2 F) {c : Fin 2 → Matrix (Fin 2) (Fin 2) F}
    (hC : gm C = bd c) {s : F} (hs : s ≠ 0) (w₀ w₁ : SL(2, F))
    (hw₀ : c 0 = s • (w₀ : Matrix (Fin 2) (Fin 2) F))
    (hw₁ : c 1 = s • (w₁ : Matrix (Fin 2) (Fin 2) F)) (x : StatedSp 2 F) :
    conjSp 2 F C x = (longBlock F 2 0 w₀ * longBlock F 2 1 w₁) * x *
      (longBlock F 2 0 w₀ * longBlock F 2 1 w₁)⁻¹ := by
  refine conjSp_eq_conj_of_eq_smul C s hs _ ?_ x
  change gm C = _
  rw [hC, map_mul, mat_longBlock_eq_bd, mat_longBlock_eq_bd, bd_mul]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [hw₀, hw₁]

end Blocks

end CFSG.ClassicalInvolution.Asc77.C5O.M
