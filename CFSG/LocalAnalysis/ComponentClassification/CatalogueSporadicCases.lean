module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.Sporadic.Schreier.Fi22Schreier
public import CFSG.Sporadic.FischerOddCore.Fi22GenFitting
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.PairMcLPairs
public import CFSG.Sporadic.Schreier.Fi24Schreier
public import CFSG.Sporadic.SuzOddCore.ExtModel
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch

public section

namespace CFSG.ComponentClassification.CatalogSchreierCases

open CFSG.ComponentClassification.SporadicSchreierDispatch

theorem sporadicSchreierCase_Fi22 : SporadicSchreierCase .Fi22 :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.Fi22.AT_Fi22_Schreier

theorem sporadicSchreierCase_He : SporadicSchreierCase .He :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.AT_He_Schreier.2.2

theorem sporadicSchreierCase_McL : SporadicSchreierCase .McL :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.AT_McL_Schreier.2

theorem sporadicSchreierCase_Fi24 : SporadicSchreierCase .Fi24Prime :=
  sporadicSchreierCase_of_outer Sporadic.Schreier.Fi24.fi24prime_outer_solvable.2

theorem sporadicSchreierCase_Suz : SporadicSchreierCase .Suz :=
  sporadicSchreierCase_of_outer Sporadic.SuzOddCore.outer_carrier_suz.2.2

end CFSG.ComponentClassification.CatalogSchreierCases

namespace CFSG.ComponentClassification.CatalogueU

open Sporadic.FischerOddCore in
theorem sporadicOddCoreFree_Fi22 : SporadicOddCoreFree .Fi22 :=
  fun _ _ _ hF _ hJ t ht =>
    CTUC_Fi22_generalized_Fitting_involution_centralizer_odd_core_trivial hF hJ t ht

theorem sporadicOddCoreFree_J3 : SporadicOddCoreFree .J3 :=
  fun _ _ _ hF _ hJ t ht =>
    Sporadic.SmallOddCore.ctuc_j3_generalized_fitting_involution_centralizer_odd_core_trivial hF hJ
      t ht

theorem sporadicOddCoreFree_Suz : SporadicOddCoreFree .Suz :=
  fun _ _ _ hF hnc ⟨e⟩ t ht =>
    (Sporadic.SuzOddCore.CTUC_Suz_model_simple_generalized_fitting_centralizer_exclusion hF hnc
      e).2 t ht

end CFSG.ComponentClassification.CatalogueU
