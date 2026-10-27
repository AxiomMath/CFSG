module

public import CFSG.LocalAnalysis.ComponentClassification.KProperComponentLocalBOpen
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergMGmatFittingTransfer
public import CFSG.Monster.SteinbergMBXInvolutionOddCore

public section

namespace CFSG.ComponentClassification.KProperRelativeB

open CFSG.Assembly CFSG.Blueprint
open CFSG.ComponentClassification.CatalogueU

theorem sporadicOddCoreFree_M
    :
    SporadicOddCoreFree .M := by
  intro X _ _ hs hnonab ⟨e⟩ t ht
  have := hs
  obtain ⟨eG⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  exact ((BMCase.gmat_generalizedFitting_transfer CFSG.RankThree.PartOne.SPOR.allInner_Gmat
    CFSG.Monster.Existence.native_M_all_involution_centralizers_odd_core_free eG).2 t ht).2

theorem kProper_component_local_B_of_frontier
    (hGH : UFrontier.GH74ModelsInput) (htriple : UFrontier.TripleBranch)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hK : KProper Catalog G)
    (hcomp : IsComponentType G) :
    oddCore G = ⊥ ∧ ComponentType.LocalBProperty G :=
  kProper_component_local_B_of_open_core
    (fun T _ _ _ hnonab he => CFSG.RankThree.PartOne.SPOR.sporadicSchreierCase_M T hnonab he)
    BMCase.sporadicOddCoreFree_B sporadicOddCoreFree_M hGH htriple G hK hcomp

end CFSG.ComponentClassification.KProperRelativeB
