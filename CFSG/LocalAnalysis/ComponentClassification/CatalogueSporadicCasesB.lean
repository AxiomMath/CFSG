module

public import CFSG.Sporadic.FischerOddCore.Fi23AlmostSimple
public import CFSG.Sporadic.Schreier.RuFStar
public import CFSG.Sporadic.SmallOddCore.HSMcL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch

public section

namespace CFSG.ComponentClassification.CatalogSchreierCases

open CFSG.ComponentClassification.SporadicSchreierDispatch

theorem sporadicSchreierCase_Fi23 : SporadicSchreierCase .Fi23 :=
  sporadicSchreierCase_of_outer Sporadic.FischerOddCore.CTUC_Fi23_Schreier.2.2

end CFSG.ComponentClassification.CatalogSchreierCases

namespace CFSG.ComponentClassification.CatalogueU

theorem sporadicOddCoreFree_Fi23 : SporadicOddCoreFree .Fi23 :=
  fun _ _ _ hF _ hJ t ht =>
    (Sporadic.FischerOddCore.CTUC_Fi23_generalized_Fitting_involution_centralizer_odd_core_trivial
      hF hJ).2 t ht

theorem sporadicOddCoreFree_Ru : SporadicOddCoreFree .Ru :=
  fun _ _ _ hF hnc hJ t ht =>
    ((Sporadic.RuSchreier.CTUC_Ru_model_simple_generalized_fitting_centralizer_exclusion hF hnc
      hJ).2 t ht).2.2.2

theorem sporadicOddCoreFree_HS : SporadicOddCoreFree .HS :=
  fun _ _ _ hF _ hJ t ht =>
    Sporadic.SmallOddCore.ctu_catalog_hs_mcl_almost_simple_odd_core_vanishing hF (.inl hJ) t ht

theorem sporadicOddCoreFree_McL : SporadicOddCoreFree .McL :=
  fun _ _ _ hF _ hJ t ht =>
    Sporadic.SmallOddCore.ctu_catalog_hs_mcl_almost_simple_odd_core_vanishing hF (.inr hJ) t ht

end CFSG.ComponentClassification.CatalogueU
