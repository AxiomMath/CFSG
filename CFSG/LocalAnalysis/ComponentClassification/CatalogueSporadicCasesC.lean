module

public import CFSG.Sporadic.Schreier.J4SCatalog
public import CFSG.Sporadic.Schreier.Co1CatalogSchreier
public import CFSG.Sporadic.Co2Schreier.Model
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.CatalogSchreierCases

open CFSG.ComponentClassification.SporadicSchreierDispatch

theorem sporadicSchreierCase_J4 : SporadicSchreierCase .J4 :=
  sporadicSchreierCase_of_outer Sporadic.J4Schreier.outer_J4_isSolvable

theorem sporadicSchreierCase_Co2 : SporadicSchreierCase .Co2 :=
  sporadicSchreierCase_of_outer Sporadic.Co2Schreier.AT_Co2_Schreier

theorem sporadicSchreierCase_Co1 : SporadicSchreierCase .Co1 := by
  obtain ⟨-, hfin, hp, -⟩ := Sporadic.Co1Schreier.catalog_schreier_of_inputs.{0}
    fun K _ e => Sporadic.Co2Schreier.AT_Co2_model_Schreier K e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hp.isNilpotent
  exact sporadicSchreierCase_of_outer (IsNilpotent.to_isSolvable (h := this))

end CFSG.ComponentClassification.CatalogSchreierCases
