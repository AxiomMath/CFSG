module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakCorr
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrFusionBridge

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type*} [Group G]

@[expose] def GSWeakMaximalComponent (J : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.MaximalComponent
    (GSGrammar.InvolutionComponent fun J K => IsPComponent 2 (J.subgroupOf K)) GSWeakReach
    (fun H => Open.fusionZStar H) J

theorem gsWeakMaximalComponent_iff_grammar {J : Subgroup G} :
    GSWeakMaximalComponent J ↔ GSGrammar.MaximalComponent
      (GSGrammar.InvolutionComponent fun J K => IsPComponent 2 (J.subgroupOf K)) GSWeakReach
      (fun H => Open.fusionZStar H) J :=
  Iff.rfl

theorem GSWeakMaximalComponent.gsMaximalComponent {J : Subgroup G}
    (h : GSWeakMaximalComponent J) : GSMaximalComponent J :=
  ⟨h.1, fun M hM => h.2 M (GSWeakReach.of_gsReach hM)⟩

end CFSG.ComponentClassification.GrSLit
