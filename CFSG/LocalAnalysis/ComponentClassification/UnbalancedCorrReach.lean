module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type*} [Group G]

@[expose] def GSReach (J L : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.Reach
    (GSGrammar.InvolutionComponent fun J K => IsPComponent 2 (J.subgroupOf K))
    UnbalancedGS.GSCorr J L

theorem gsReach_iff_grammar {J L : Subgroup G} :
    GSReach J L ↔ GSGrammar.Reach
      (GSGrammar.InvolutionComponent fun J K => IsPComponent 2 (J.subgroupOf K))
      UnbalancedGS.GSCorr J L :=
  Iff.rfl

theorem GSReach.of_gsCorr {a b : G} {J L : Subgroup G} (h : UnbalancedGS.GSCorr a J b L) :
    GSReach J L :=
  gsReach_iff_grammar.2 <|
    GSGrammar.Reach.single (UnbalancedGS.gsCorr_iff_grammar.1 h).involutionComponent_left h

theorem GSReach.tail {a b : G} {J₀ J L : Subgroup G} (h : GSReach J₀ J)
    (hC : UnbalancedGS.GSCorr a J b L) : GSReach J₀ L :=
  gsReach_iff_grammar.2 <| (gsReach_iff_grammar.1 h).tail hC

theorem GSReach.trans {J₀ J L : Subgroup G} (h₁ : GSReach J₀ J) (h₂ : GSReach J L) :
    GSReach J₀ L :=
  gsReach_iff_grammar.2 <| (gsReach_iff_grammar.1 h₁).trans (gsReach_iff_grammar.1 h₂)

theorem GSReach.refl_of_gsUnbalancingTriple {a x : G} {J : Subgroup G}
    (hU : GSUnbalancingTriple a x J) : GSReach J J :=
  gsReach_iff_grammar.2 <|
    GSGrammar.Reach.refl (gsUnbalancingTriple_iff_grammar.1 hU).involutionComponent

end CFSG.ComponentClassification.UnbalancedCorr
