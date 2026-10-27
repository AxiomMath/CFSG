module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Aut
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5 Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

namespace CFSG.GH74.Ivk413

variable {F : Type} [Field F]

@[expose] noncomputable def eLin (F : Type) [Field F] : projectiveSL 4 F ≃* PG (ModelData.lin F) :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 F).symm.trans
    (projectiveSpecialLinearGroupEquivStatedProj 4 F)

theorem eLin_proj (g₀ : SpecialLinearGroup (Fin 4) F) :
    eLin F (proj 4 F g₀) = mkP (ModelData.lin F) (specialLinearGroupEquivStatedSL 4 F g₀) := rfl

theorem mem_semilinear_of_odd [Finite F] {α : MulAut (projectiveSL 4 F)} (hα : Odd (orderOf α)) :
    α ∈ semilinearAutGroup 4 F :=
  mem_semilinearAutGroup_of_pow_odd (by norm_num) hα (pow_orderOf_eq_one α)

theorem semiRep_lin [Finite F] : SemiRep (ModelData.lin F) := by
  intro β hodd
  let β' : MulAut (projectiveSL 4 F) := MulAut.congr (eLin F).symm β
  have hβ' : ∀ x, eLin F (β' x) = β (eLin F x) := fun x => by
    simp [β', MulAut.congr_apply]
  have hodd' : Odd (orderOf β') := by
    rw [MulEquiv.orderOf_eq (MulAut.congr (eLin F).symm)]
    exact hodd
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.1 (mem_semilinear_of_odd hodd')
  refine ⟨A, σ, Subgroup.mem_top _, fun g => ?_⟩
  obtain ⟨g₀, rfl⟩ := (specialLinearGroupEquivStatedSL 4 F).surjective g
  have hmat : ((A * glAut σ ((specialLinearGroupEquivStatedSL 4 F g₀ : GL (Fin 4) F)) * A⁻¹ :
      GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((CatalogueBHigherLinearAction.slConjugation 4 F A (SpecialLinearGroup.map σ.toRingHom g₀) :
        SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [coe_slConjugation, Units.val_mul, Units.val_mul, coe_glAut,
      specialLinearGroupEquivStatedSL_coe]
    rfl
  have hgm : A * glAut σ ((specialLinearGroupEquivStatedSL 4 F g₀ : GL (Fin 4) F)) * A⁻¹ =
      ((specialLinearGroupEquivStatedSL 4 F (CatalogueBHigherLinearAction.slConjugation 4 F A
        (SpecialLinearGroup.map σ.toRingHom g₀)) : ↥(StatedSL 4 F)) : GL (Fin 4) F) := by
    apply Units.ext
    rw [hmat]
    rfl
  have hg : A * glAut σ ((specialLinearGroupEquivStatedSL 4 F g₀ : GL (Fin 4) F)) * A⁻¹ ∈
      (ModelData.lin F).K4 := by
    rw [hgm]
    exact (specialLinearGroupEquivStatedSL 4 F _).2
  refine ⟨hg, ?_⟩
  have h1 : β (mkP (ModelData.lin F) (specialLinearGroupEquivStatedSL 4 F g₀)) =
      mkP (ModelData.lin F) (specialLinearGroupEquivStatedSL 4 F
        (CatalogueBHigherLinearAction.slConjugation 4 F A
          (SpecialLinearGroup.map σ.toRingHom g₀))) := by
    rw [← eLin_proj, ← hβ', hAσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj, eLin_proj]
  rw [h1]
  congr 1
  exact Subtype.ext hgm.symm

theorem hdet_lin : ∀ C ∈ (ModelData.lin F).U4,
    sc4 (Matrix.GeneralLinearGroup.det C) ∈ (ModelData.lin F).U4 :=
  fun _ _ => Subgroup.mem_top _

theorem hphiU_lin : ∀ (φ : F ≃+* F) (C : GL (Fin 4) F), C ∈ (ModelData.lin F).U4 →
    glAut φ C ∈ (ModelData.lin F).U4 :=
  fun _ _ _ => Subgroup.mem_top _

theorem hphi_lin : ∀ φ : F ≃+* F, (∀ a ∈ (ModelData.lin F).H2,
    φ ((a : Matrix (Fin 2) (Fin 2) F).trace) = (a : Matrix (Fin 2) (Fin 2) F).trace) →
      ∀ x, φ (φ x) = x := by
  intro φ hφ
  have hfix : ∀ t, φ t = t := by
    intro t
    let g : SpecialLinearGroup (Fin 2) F := ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
    have hg : (SpecialLinearGroup.toGL g : GL (Fin 2) F) ∈ (ModelData.lin F).H2 := by
      rw [(ModelData.lin F).mem_H2]
      refine ⟨Subgroup.mem_top _, ?_⟩
      rw [SpecialLinearGroup.coe_GL_coe_matrix]
      exact g.2
    have := hφ _ hg
    rw [SpecialLinearGroup.coe_GL_coe_matrix] at this
    simpa [g, Matrix.trace, Fin.sum_univ_two] using this
  intro x
  rw [hfix, hfix]

theorem autInner_lin [Finite F] (hG : GoodModel (ModelData.lin F)) : AutInner (ModelData.lin F) :=
  autInner_of_semiRep hG semiRep_lin hdet_lin hphiU_lin hphi_lin

end CFSG.GH74.Ivk413
