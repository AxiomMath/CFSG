module

public import CFSG.LocalAnalysis.ComponentClassification.KProperComponentLocalBFrontier
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.FooteLit

theorem catalogAlmostSimpleUnbalancedOutcome_holds
    : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome :=
  CatalogueU.catalogAlmostSimpleUnbalancedOutcome_of_checks CatalogueU.evenExceptionalCheck
    Sporadic.Schreier.LargeReeExcl.CTU_catalog_large_Ree_Tits_check_holds
    (CatalogueU.sporadicNonJ1Check_of_remaining CatalogueU.sporadicOddCoreFree_J3
      CatalogueU.sporadicOddCoreFree_J4 CatalogueU.sporadicOddCoreFree_Co1
      Sporadic.Co2Schreier.sporadicOddCoreFree_Co2 Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
      CatalogueU.sporadicOddCoreFree_Fi22 CatalogueU.sporadicOddCoreFree_Fi23
      CatalogueU.sporadicOddCoreFree_Fi24Prime CatalogueU.sporadicOddCoreFree_HS
      CatalogueU.sporadicOddCoreFree_McL CatalogueU.sporadicOddCoreFree_Ru
      CatalogueU.sporadicOddCoreFree_Suz Sporadic.ONOddCore.sporadicOddCoreFree_ONan
      Sporadic.HNOddCore.sporadicOddCoreFree_HN Sporadic.LySchreier.sporadicOddCoreFree_Ly
      Sporadic.ThSchreier.sporadicOddCoreFree_Th BMCase.sporadicOddCoreFree_B
      KProperRelativeB.sporadicOddCoreFree_M CatalogueU.heldUnbalancedOutcome)

end CFSG.ComponentClassification.FooteLit
