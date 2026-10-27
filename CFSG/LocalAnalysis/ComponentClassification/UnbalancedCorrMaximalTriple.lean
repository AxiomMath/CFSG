module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type*} [Group G]

@[expose] def GSMaximalUnbalancingTriple (a x : G) (J : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.MaximalUnbalancingTriple GSUnbalancingTriple UnbalancedGS.GSCorr
    UnbalancedGS.GSIsoCorr a x J

theorem gsMaximalUnbalancingTriple_iff_grammar {a x : G} {J : Subgroup G} :
    GSMaximalUnbalancingTriple a x J ↔ GSGrammar.MaximalUnbalancingTriple GSUnbalancingTriple
      UnbalancedGS.GSCorr UnbalancedGS.GSIsoCorr a x J :=
  Iff.rfl

end CFSG.ComponentClassification.UnbalancedCorr
