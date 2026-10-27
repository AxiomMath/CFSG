module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierBranches
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueEvenExceptionalCheck
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.Schreier.LargeReeExclCatalog
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.Sporadic.HeldB.AlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases

public section

namespace CFSG.ComponentClassification.CatalogueU

theorem heldUnbalancedOutcome : HeldUnbalancedOutcome := by
  intro X _ _ hs hnab hiso hz
  obtain ⟨z, hz2, hzc⟩ := hz
  have hzc' : CFSG.pPrimeCore 2 (Subgroup.centralizer ({z} : Set X)) ≠ ⊥ := by
    rwa [← UFrontier.oddCore_eq_pPrimeCore_two']
  exact ((Sporadic.HeldB.Held_almost_simple_inner_involution_exclusion_of_outer
      CFSG.Sporadic.Schreier.AT_He_Schreier.1 hs hnab hiso).2.2 z hz2 hzc').2.2.2

theorem sporadicNonJ1Check_of_BM (oB : SporadicOddCoreFree .B) (oM : SporadicOddCoreFree .M) :
    SporadicNonJ1Check :=
  sporadicNonJ1Check_of_remaining sporadicOddCoreFree_J3 sporadicOddCoreFree_J4
    sporadicOddCoreFree_Co1 Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
    Sporadic.SmallOddCore.sporadicOddCoreFree_Co3 sporadicOddCoreFree_Fi22
    sporadicOddCoreFree_Fi23 sporadicOddCoreFree_Fi24Prime sporadicOddCoreFree_HS
    sporadicOddCoreFree_McL sporadicOddCoreFree_Ru sporadicOddCoreFree_Suz
    Sporadic.ONOddCore.sporadicOddCoreFree_ONan Sporadic.HNOddCore.sporadicOddCoreFree_HN
    Sporadic.LySchreier.sporadicOddCoreFree_Ly Sporadic.ThSchreier.sporadicOddCoreFree_Th oB oM
    heldUnbalancedOutcome

theorem catalogAlmostSimpleUnbalancedOutcome_of_BM (oB : SporadicOddCoreFree .B)
    (oM : SporadicOddCoreFree .M) : CatalogAlmostSimpleUnbalancedOutcome :=
  catalogAlmostSimpleUnbalancedOutcome_of_checks evenExceptionalCheck
    Sporadic.Schreier.LargeReeExcl.CTU_catalog_large_Ree_Tits_check_holds
    (sporadicNonJ1Check_of_BM oB oM)

end CFSG.ComponentClassification.CatalogueU
