module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.SeitzReduction.SymplecticPilot
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open Matrix

variable {F : Type} [Field F]

@[expose] noncomputable def sp4Diag : Fˣ →* StatedSp 2 F :=
  (diagSp F 2).comp (MonoidHom.mulSingle (fun _ : Fin 2 => Fˣ) 0)

@[expose] noncomputable def sp4Tor : Fˣ →* StatedProj (StatedSp 2 F) :=
  (proj 2 F).comp sp4Diag

theorem mat_sp4Diag_inl_zero (c : Fˣ) : mat 2 F (sp4Diag c) (Sum.inl 0) (Sum.inl 0) = c := by
  simp [sp4Diag, mat_diagSp_apply]

theorem mat_sp4Diag_inl_one (c : Fˣ) : mat 2 F (sp4Diag c) (Sum.inl 1) (Sum.inl 1) = 1 := by
  simp [sp4Diag, mat_diagSp_apply]

theorem sp4Tor_injective : Function.Injective (sp4Tor (F := F)) := by
  intro a b hab
  have h1 : (sp4Diag a)⁻¹ * sp4Diag b ∈ spScalars 2 F := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv]
    have : proj 2 F (sp4Diag a) = proj 2 F (sp4Diag b) := hab
    rw [this, inv_mul_cancel]
  rw [← map_inv, ← map_mul] at h1
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨c, hc⟩ := h1
  have e1 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) F =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 1) (Sum.inl 1)) hc
  have e0 := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) F =>
    (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inl 0)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    at e1 e0
  have hm1 := mat_sp4Diag_inl_one (F := F) (a⁻¹ * b)
  have hm0 := mat_sp4Diag_inl_zero (F := F) (a⁻¹ * b)
  rw [mat_apply] at hm1 hm0
  have hc1 : (c : F) = 1 := e1.trans hm1
  have hab1 : ((a⁻¹ * b : Fˣ) : F) = 1 := hm0.symm.trans (e0.symm.trans hc1)
  exact inv_mul_eq_one.mp (Units.ext hab1)

theorem fieldSp_sp4Diag (σ : F ≃+* F) (c : Fˣ) :
    fieldSp 2 F σ (sp4Diag c) = sp4Diag (Units.map (σ : F →* F) c) := by
  apply mat_injective
  have h1 : mat 2 F (fieldSp 2 F σ (sp4Diag c)) = (mat 2 F (sp4Diag c)).map σ := by
    rw [mat_apply, mat_apply, coe_fieldSp]
  rw [h1]
  simp only [sp4Diag, MonoidHom.comp_apply, mat_diagSp]
  rw [Matrix.diagonal_map (by simp)]
  congr 1
  funext a
  rcases a with i | i
  · fin_cases i <;> simp [diagSpEntry]
  · fin_cases i <;> simp [diagSpEntry]

theorem fieldAut_sp4Tor (σ : F ≃+* F) (c : Fˣ) :
    fieldAut 2 F σ (sp4Tor c) = sp4Tor (Units.map (σ : F →* F) c) := by
  rw [sp4Tor, MonoidHom.comp_apply, fieldAut_proj, fieldSp_sp4Diag]
  rfl

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
