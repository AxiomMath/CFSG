module

public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBRemaining
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.Milestones.CL_LIT_Aschbacher_proper_two_generated_core
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUBM
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierLowRank
public import CFSG.Sporadic.Schreier.LySchreierCase
public import CFSG.Sporadic.HeldB.IndexTwo
public import CFSG.Sporadic.HNSchreier.Schreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC

public section

namespace CFSG.ComponentClassification.KProperRelativeB

open CFSG.Assembly CFSG.Blueprint
open CFSG.ComponentClassification.SporadicSchreierDispatch (SporadicSchreierCase
  sporadicSchreierCase_of_outer)
open CFSG.ComponentClassification.CatalogSchreierCases
open CFSG.ComponentClassification.CatalogueU

theorem heldInput : HeldInput := fun G _ _ hs hnonab hidx hiso hproper =>
  (@Sporadic.HeldB.Held_index_two_B_under_proper_subgroup_B G _ _ hs
    hnonab hidx hiso hproper).2

theorem kProper_component_local_B_of_open
    (hB : SporadicSchreierCase .B) (hM : SporadicSchreierCase .M)
    (oB : SporadicOddCoreFree .B) (oM : SporadicOddCoreFree .M)
    (hasc : UFrontier.AschbacherCoreInput)
    (hGH : UFrontier.GH74ModelsInput) (htriple : UFrontier.TripleBranch)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hK : KProper Catalog G)
    (hcomp : IsComponentType G) :
    oddCore G = ⊥ ∧ ComponentType.LocalBProperty G := by
  have hCU := catalogAlmostSimpleUnbalancedOutcome_of_BM oB oM
  have hU := UFrontier.relativeU_of_tripleBranch hCU UFrontier.lowTwoRankCatalogInput hasc hGH
    htriple
  exact kProper_component_local_B_of_remaining tits_model_outer_solvable sporadicSchreierCase_J2
    sporadicSchreierCase_J3 sporadicSchreierCase_J4 sporadicSchreierCase_Co1
    sporadicSchreierCase_Co2 sporadicSchreierCase_Co3 sporadicSchreierCase_Fi22
    sporadicSchreierCase_Fi23 sporadicSchreierCase_Fi24 sporadicSchreierCase_HS
    sporadicSchreierCase_McL sporadicSchreierCase_He sporadicSchreierCase_Ru
    sporadicSchreierCase_Suz sporadicSchreierCase_ON
    (sporadicSchreierCase_of_outer Sporadic.HNSchreier.AT_HN_Schreier)
    Sporadic.LySchreier.sporadicSchreierCase_Ly
    Sporadic.ThSchreier.sporadicSchreierCase_Th hB hM hU heldInput G hK hcomp

theorem kProper_component_local_B_of_open_core
    (hM : SporadicSchreierCase .M) (oB : SporadicOddCoreFree .B) (oM : SporadicOddCoreFree .M)
    (hGH : UFrontier.GH74ModelsInput) (htriple : UFrontier.TripleBranch)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hK : KProper Catalog G)
    (hcomp : IsComponentType G) :
    oddCore G = ⊥ ∧ ComponentType.LocalBProperty G :=
  kProper_component_local_B_of_open BMCase.sporadicSchreierCase_B hM oB oM
    (fun G _ _ _ hnonab S hrank hcore =>
      CFSG.Milestones.cl_lit_aschbacher_proper_two_generated_core G hnonab S hrank hcore)
    hGH htriple G hK hcomp

end CFSG.ComponentClassification.KProperRelativeB
