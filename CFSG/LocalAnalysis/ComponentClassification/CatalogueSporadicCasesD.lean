module

public import CFSG.Sporadic.Schreier.Co1OddCore
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.CatalogueU

theorem sporadicOddCoreFree_Co1 : SporadicOddCoreFree .Co1 :=
  Sporadic.Co1Schreier.OddCore.sporadicOddCoreFree_Co1_of_inputs
    Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner
    Sporadic.Co2Schreier.CTUC_Co2_all_involution_centralizers_odd_core_free

open Sporadic.FischerOddCore in
theorem sporadicOddCoreFree_Fi24Prime : SporadicOddCoreFree .Fi24Prime :=
  fun _ _ _ hF _ hJ t ht =>
    (CTUC_Fi24prime_generalized_Fitting_involution_centralizer_odd_core_trivial hF hJ).2 t ht

end CFSG.ComponentClassification.CatalogueU
