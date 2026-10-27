module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingFusionCorrBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrReach
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrMaximalTriple

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type*} [Group G]

@[expose] def GSMaximalComponent (J : Subgroup G) : Prop :=
  gs_grammar% GSGrammar.MaximalComponent
    (GSGrammar.InvolutionComponent fun J K => IsPComponent 2 (J.subgroupOf K)) GSReach
    (fun H => Open.fusionZStar H) J

theorem gsMaximalComponent_iff_grammar {J : Subgroup G} :
    GSMaximalComponent J ↔ GSGrammar.MaximalComponent
      (GSGrammar.InvolutionComponent fun J K => IsPComponent 2 (J.subgroupOf K)) GSReach
      (fun H => Open.fusionZStar H) J :=
  Iff.rfl

theorem fusionOddCoreOf_eq (X : Subgroup G) :
    Open.fusionOddCoreOf X = (pPrimeCore 2 X).map X.subtype :=
  congrFun UnbalancingLocal.fusionOddCoreOf_eq_map_pPrimeCore X

alias fusionIsSylowIn_iff := Open.fusionIsSylowIn_iff

variable [Finite G]

theorem fusionIsInvolutionTwoComponent_iff {J : Subgroup G} :
    Open.fusionIsInvolutionTwoComponent J ↔ ∃ a : G, orderOf a = 2 ∧
      J ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) :=
  Open.fusionIsInvolutionTwoComponent_iff_grammar.trans <|
    GSGrammar.involutionComponent_congr fun _ _ => UnbalancingLocal.fusionTwoComponentCond_iff

theorem fusionIsoCorr_iff_gsIsoCorr {a b : G} {J L : Subgroup G} :
    Open.fusionIsoCorr a J b L ↔ UnbalancedGS.GSIsoCorr a J b L :=
  Open.fusionIsoCorr_iff_grammar.trans <| (GSGrammar.isoCorr_congr
    (fun _ _ _ _ => UnbalancingLocal.fusionCorr_iff_gsCorr)
    UnbalancingLocal.fusionOddCoreOf_eq_map_pPrimeCore
    UnbalancingLocal.fusionFixedLayer_eq_gsFixedLayer).trans UnbalancedGS.gsIsoCorr_iff_grammar.symm

theorem fusionUnbalancingTriple_iff {a x : G} {J : Subgroup G} :
    Open.fusionUnbalancingTriple a x J ↔ GSUnbalancingTriple a x J :=
  Open.fusionUnbalancingTriple_iff_grammar.trans <| (GSGrammar.unbalancingTriple_congr
    (fun _ _ => UnbalancingLocal.fusionTwoComponentCond_iff)
    UnbalancingLocal.fusionOddCoreOf_eq_map_pPrimeCore).trans gsUnbalancingTriple_iff_grammar.symm

theorem fusionReach_iff_gsReach {J L : Subgroup G} :
    Open.fusionReach J L ↔ GSReach J L :=
  Open.fusionReach_iff_grammar.trans <| (GSGrammar.reach_congr
    (fun _ => fusionIsInvolutionTwoComponent_iff)
    fun _ _ _ _ => UnbalancingLocal.fusionCorr_iff_gsCorr).trans gsReach_iff_grammar.symm

theorem fusionMaximalUnbalancingTriple_iff {a x : G} {J : Subgroup G} :
    Open.fusionMaximalUnbalancingTriple a x J ↔ GSMaximalUnbalancingTriple a x J :=
  Open.fusionMaximalUnbalancingTriple_iff_grammar.trans <|
    (GSGrammar.maximalUnbalancingTriple_congr
    (fun _ _ _ => fusionUnbalancingTriple_iff)
    (fun _ _ _ _ => UnbalancingLocal.fusionCorr_iff_gsCorr)
    fun _ _ _ _ => fusionIsoCorr_iff_gsIsoCorr).trans gsMaximalUnbalancingTriple_iff_grammar.symm

theorem fusionMaximalComponent_iff {J : Subgroup G} :
    Open.fusionMaximalComponent J ↔ GSMaximalComponent J :=
  Open.fusionMaximalComponent_iff_grammar.trans <| (GSGrammar.maximalComponent_congr
    (fun _ => fusionIsInvolutionTwoComponent_iff)
    fun _ _ => fusionReach_iff_gsReach).trans gsMaximalComponent_iff_grammar.symm

end CFSG.ComponentClassification.UnbalancedCorr
