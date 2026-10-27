module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageModelsHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuousAltSixHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuousU33Holds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuousTitsHolds
public import CFSG.LieType.ChevTwo.ModelSplitHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviOfPackage

public section

namespace CFSG.GroupTheory

open CFSG.Open


theorem gomiChevLeviPackage_holds (hSp : GomiLeviFactorsSp) (hSU : GomiLeviFactorsSU)
    (hSpinPlus : GomiLeviFactorsSpinPlus) (hSpinMinus : GomiLeviFactorsSpinMinus)
    (hF4 : GomiLeviFactorsF4) (hE6 : GomiLeviFactorsE6) (hE7 : GomiLeviFactorsE7)
    (hE8 : GomiLeviFactorsE8) (hE6tw : GomiLeviFactorsTwistedE6) : GomiChevLeviPackage :=
  gomiChevLeviPackage_of_models CFSG.LieType.ChevTwo.chevTwoModelSplit_holds
    (gomiChevLeviPackageModel_holds hSp hSU hSpinPlus hSpinMinus hF4 hE6 hE7 hE8 hE6tw)
    (fun _ _ _ _ _ => gomiAtomsOnlyTop_of_lieModel_tits)
    (fun _ _ _ ⟨e⟩ => gomiAtomsOnlyTop_of_mulEquiv_alternatingGroup_six e)
    (fun _ _ _ => gomiAtomsOnlyTop_of_psu_three_three)

theorem gomiChevLeviDecomposition_holds (hSp : GomiLeviFactorsSp) (hSU : GomiLeviFactorsSU)
    (hSpinPlus : GomiLeviFactorsSpinPlus) (hSpinMinus : GomiLeviFactorsSpinMinus)
    (hF4 : GomiLeviFactorsF4) (hE6 : GomiLeviFactorsE6) (hE7 : GomiLeviFactorsE7)
    (hE8 : GomiLeviFactorsE8) (hE6tw : GomiLeviFactorsTwistedE6) : GomiChevLeviDecomposition :=
  gomiChevLeviDecomposition_of_gomiChevLeviPackage
    (gomiChevLeviPackage_holds hSp hSU hSpinPlus hSpinMinus hF4 hE6 hE7 hE8 hE6tw)

end CFSG.GroupTheory
