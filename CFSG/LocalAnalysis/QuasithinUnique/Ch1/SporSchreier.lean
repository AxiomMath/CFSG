module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreierList
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.RuModel

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.ComponentClassification
open CFSG.ComponentClassification.SporadicSchreierDispatch (SporadicSchreierCase)

theorem sporadicSchreierCase_He
    : SporadicSchreierCase .He :=
  SporadicSchreierDispatch.sporadicSchreierCase_of_outer
    CFSG.Sporadic.Schreier.AT_He_Schreier.2.2

theorem sporadicSchreierCase_Ru
    : SporadicSchreierCase .Ru :=
  SporadicSchreierDispatch.sporadicSchreierCase_of_outer
    CFSG.Sporadic.RuSchreier.AT_Ru_model_Schreier.{0}.1

theorem schreierFactListCat_of_J4
    (hJ4 : SporadicSchreierCase .J4) : SchreierFactListCat :=
  schreierFactListCat_of_cases hJ4 sporadicSchreierCase_He sporadicSchreierCase_Ru

end CFSG.QuasithinUnique.Vol2Native
