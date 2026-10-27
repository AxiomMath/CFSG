module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularBridge
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLevi
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootQ1
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogue
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootHolds
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLie

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree


theorem twE6DiagRegularGen_of_open (hQ2 : TwE6LongRootIrreducible) (hQ4 : TwE6LongRootGenerates)
    (hL : TwE6InnerLineLie) (hcat : TwE6LeviCatalogue) : TwE6DiagRegularGen :=
  twE6DiagRegularGen_of_longRoot TwE6LongRoot.q1_holds hQ2 hQ4
    (twE6InnerLineLongRoot_of_lie twE6LiftBridge_holds hL)
    (twE6LeviPlaneGeneration_of_catalogue hcat)

theorem twE6DiagRegularGen_of_long (hQ2 : TwE6LongRootIrreducible) (hQ4 : TwE6LongRootGenerates)
    (hL : TwE6InnerLineLie) : TwE6DiagRegularGen :=
  twE6DiagRegularGen_of_open hQ2 hQ4 hL twE6LeviCatalogue_holds

theorem twE6DiagRegularGen_of_innerLine (hL : TwE6InnerLineLie) : TwE6DiagRegularGen :=
  twE6DiagRegularGen_of_long twE6LongRootIrreducible_holds twE6LongRootGenerates_holds hL

theorem twE6DiagRegularGen_holds : TwE6DiagRegularGen :=
  twE6DiagRegularGen_of_innerLine twE6InnerLineLie_holds

end CFSG.LieType.SeitzGeneration.ExcWideThree
