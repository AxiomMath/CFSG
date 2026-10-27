module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Core

public section

namespace CFSG.ComponentClassification.GrSLit

theorem isL34Type_of_gsWeakCorr {G : Type} [Group G] {a b : G} {J M : Subgroup G}
    (hJ : GSWeakMaximalComponent J) (hC : GSWeakCorr a J b M)
    (htype : IsL34Type (J ⧸ Open.fusionZStar J)) : IsL34Type (M ⧸ Open.fusionZStar M) := by
  obtain ⟨e⟩ := hJ.2 M (GSWeakReach.single hC)
  exact LieType.CurtisTits.lieModel_of_mulEquiv e htype

end CFSG.ComponentClassification.GrSLit

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma55TypeStep_of_weakMaximal
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hWM : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
      L34Sec5Setting G L t S T → GSWeakMaximalComponent L) :
    L34Lemma55TypeStep := by
  intro G _ _ L t S T hset z hzQ hz M hMz hMp hMt hTM
  have hset' := hset
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -⟩, -⟩ := hset'
  obtain ⟨hzS, hzK⟩ := mem_inf.mp hzQ
  have htz : t * z = z * t := (hZS z hzS).symm
  obtain ⟨hzN, hzC⟩ := mem_coreActionKernel.mp hzK
  have hW : GSWeakCorr t L z M := ⟨hto, hz, htz, hLt, hLpt, hMz, hMp, hzN, hzC, by
    rw [hMt, sup_idem]
    exact hTM⟩
  exact isL34Type_of_gsWeakCorr (hWM G L t S T hset) hW htypeL

theorem l34Lemma55TypeStep_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput) :
    L34Lemma55TypeStep :=
  l34Lemma55TypeStep_of_weakMaximal hS hU hheld hSol hGW fun _ _ _ _ _ _ _ hset =>
    hset.2.1.2.2.1

end CFSG.ComponentClassification.HSFLit.L34Inv
