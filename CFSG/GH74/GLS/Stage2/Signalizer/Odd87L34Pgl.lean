module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs
public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
import CFSG.Adapters.LinearSmallCatalog
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Certificates.Certificate2022
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

open Subgroup CFSG.ComponentClassification.PSL3Four CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace L34Pgl

open Odd87L34Out (NN)

theorem rho_scalar (u : F4ˣ) : rho (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = 1 :=
  Equiv.ext fun i => rhoFun_scalar (c := (u : F4)) u.ne_zero rfl i

@[expose] def rhoBar : Matrix.ProjGenLinGroup (Fin 3) F4 →* Equiv.Perm (Fin 42) :=
  Matrix.ProjGenLinGroup.lift rho (MonoidHom.ext fun u => rho_scalar u)

theorem rhoBar_mk (A : GL (Fin 3) F4) : rhoBar (Matrix.ProjGenLinGroup.mk A) = rho A := rfl

theorem theta_conjAut (A : GL (Fin 3) F4)
    (x : LinearFlag.projectiveSL 3 F4) :
    (theta (LinearFlag.conjAut 3 F4 A x) : Equiv.Perm (Fin 42)) =
      rho A * theta x * (rho A)⁻¹ := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 F4 x
  rw [LinearFlag.conjAut_proj, theta_proj, theta_proj,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
    map_mul, map_inv]

theorem exists_scalar_of_rho_eq_one {A : GL (Fin 3) F4}
    (h : rho A = 1) : ∃ c : F4ˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = A := by
  have hc : LinearFlag.conjAut 3 F4 A = 1 := by
    refine MulEquiv.ext fun x => theta.injective (Subtype.ext ?_)
    rw [theta_conjAut, h]
    simp
  obtain ⟨-, c, hc'⟩ := LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) (by norm_num)
    A 1 (by rw [map_one, mul_one, hc])
  exact ⟨c, hc'⟩

theorem rhoBar_injective : Function.Injective rhoBar := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  induction x using Matrix.ProjGenLinGroup.induction_on with | mk A =>
  rw [MonoidHom.mem_ker, rhoBar_mk] at hx
  obtain ⟨c, rfl⟩ := exists_scalar_of_rho_eq_one hx
  rw [Matrix.ProjGenLinGroup.mk_scalar]
  exact Subgroup.one_mem _

theorem rho_mem_NN (A : GL (Fin 3) F4) : rho A ∈ NN := by
  have hdet : (A : Matrix (Fin 3) (Fin 3) F4).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit A) |>.ne_zero
  have hcases : ∀ x : F4, x ≠ 0 → x = 1 ∨ x = F4.ω ∨ x = F4.ω * F4.ω := by decide
  have hg4 : rho dGL ∈ NN := Subgroup.mem_sup_right (mem_zpowers g₄)
  have hS : ∀ B : GL (Fin 3) F4, (B : Matrix (Fin 3) (Fin 3) F4).det = 1 → rho B ∈ NN :=
    fun B hB => Subgroup.mem_sup_left (rho_mem_S_of_det hB)
  rcases hcases _ hdet with h | h | h
  · exact hS A h
  · have hB : ((A * dGL⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, h, det_dGL_inv]
      decide
    have := Subgroup.mul_mem _ (hS _ hB) hg4
    rwa [← map_mul, inv_mul_cancel_right] at this
  · have hB : ((A * dGL⁻¹ * dGL⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, h, det_dGL_inv]
      decide
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (hS _ hB) hg4) hg4
    rwa [← map_mul, ← map_mul, inv_mul_cancel_right, inv_mul_cancel_right] at this

theorem range_rhoBar : rhoBar.range = NN := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨x, rfl⟩
    induction x using Matrix.ProjGenLinGroup.induction_on with | mk A =>
    rw [rhoBar_mk]
    exact rho_mem_NN A
  · rw [← range_rhoSL.1]
    rintro _ ⟨A, rfl⟩
    exact ⟨Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A), rfl⟩
  · rw [zpowers_le]
    exact ⟨Matrix.ProjGenLinGroup.mk dGL, rfl⟩

end L34Pgl

theorem isPGL3Four_NN : IsPGL3Four ↥Odd87L34Out.NN :=
  ⟨F4, inferInstance, inferInstance, natCard_F4,
    ⟨(MulEquiv.subgroupCongr L34Pgl.range_rhoBar).symm.trans
      (MonoidHom.ofInjective L34Pgl.rhoBar_injective).symm⟩⟩

theorem isL2_four_C₃ :
    IVK.IsL2 ↥CFSG.ComponentClassification.PSL3Four.C₃ (fun q => q = 4) := by
  have : IsSimpleGroup ↥C₃ := isSimpleGroup_C₃
  obtain ⟨e₁⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    card_C₃
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F4) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [natCard_F4])
  obtain ⟨e₂⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F4)
    (CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four F4 natCard_F4)
  exact ⟨F4, inferInstance, inferInstance, natCard_F4,
    ⟨e₁.trans (e₂.symm.trans (IVK.L2.equivPSL F4).symm)⟩⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
