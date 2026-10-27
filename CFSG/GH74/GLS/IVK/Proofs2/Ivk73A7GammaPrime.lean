module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAction
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK

open CFSG Subgroup Equiv Equiv.Perm
open CFSG.ComponentClassification.HSFLit CFSG.ComponentClassification.TBLit
open scoped Pointwise

abbrev Alt7 := alternatingGroup (Fin 7)

noncomputable def sigmaOfAction {E : Type*} [Group E] (rho : E →* MulAut Alt7) :
    E →* Equiv.Perm (Fin 7) :=
  CFSG.ComponentClassification.HSFLit.permEquivAutA7.symm.toMonoidHom.comp rho

@[simp]
theorem permEquivAutA7_sigmaOfAction {E : Type*} [Group E] (rho : E →* MulAut Alt7) (e : E) :
    CFSG.ComponentClassification.HSFLit.permEquivAutA7 (sigmaOfAction rho e) = rho e := by
  simp [sigmaOfAction]

section SourceAdapter

variable {G : Type*} [Group G] (J : Subgroup G)

noncomputable def sourceQuotAction {E : Subgroup G} (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    E →* MulAut (J ⧸ CFSG.pPrimeCore 2 J) :=
  (CFSG.ComponentClassification.TBLit.oddQuotAction J).comp (Subgroup.inclusion hEJ)

noncomputable def sourceAction
    (e : J ⧸ CFSG.pPrimeCore 2 J ≃* Alt7) {E : Subgroup G}
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) : E →* MulAut Alt7 :=
  (MulAut.congr e).toMonoidHom.comp (sourceQuotAction J hEJ)

noncomputable def sourceSigma
    (e : J ⧸ CFSG.pPrimeCore 2 J ≃* Alt7) {E : Subgroup G}
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) : E →* Equiv.Perm (Fin 7) :=
  sigmaOfAction (sourceAction J e hEJ)

@[simp]
theorem sigmaOfAction_sourceAction
    (e : J ⧸ CFSG.pPrimeCore 2 J ≃* Alt7) {E : Subgroup G}
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    sigmaOfAction (sourceAction J e hEJ) = sourceSigma J e hEJ := by
  rfl

@[simp]
theorem permEquivAutA7_sourceSigma
    (e : J ⧸ CFSG.pPrimeCore 2 J ≃* Alt7) {E : Subgroup G}
    (hEJ : E ≤ Subgroup.normalizer (J : Set G)) (q : E) :
    permEquivAutA7 (sourceSigma J e hEJ q) = sourceAction J e hEJ q := by
  rw [← sigmaOfAction_sourceAction]
  exact permEquivAutA7_sigmaOfAction (sourceAction J e hEJ) q

end SourceAdapter

end CFSG.GH74.GLS.IVK
