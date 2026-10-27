module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Sporadic.J4
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch

public section

namespace CFSG.QuasithinUnique

open CFSG.ComponentClassification.SporadicSchreierDispatch (SporadicSchreierCase)

theorem sporadicSchreierCase_J4_of_outOdd
    (h : Ch1.J4OutOdd) : SporadicSchreierCase .J4 := by
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.fam_j4_simplicity.1
  have : Finite (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J4)) :=
    Finite.of_injective (fun α : MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J4) =>
      (α : CFSG.Blueprint.NativeSporadic.Carrier .J4 → CFSG.Blueprint.NativeSporadic.Carrier .J4))
      DFunLike.coe_injective
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Blueprint.NativeSporadic.Carrier .J4)) :=
    Finite.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact CFSG.ComponentClassification.SporadicSchreierDispatch.sporadicSchreierCase_of_outer
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ h)

end CFSG.QuasithinUnique
