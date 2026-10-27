module

public import CFSG.LieType.SeitzGeneration.ClassicalAssemblyClosed
public import CFSG.LieType.SeitzGeneration.OuterNarrowClassical
public import CFSG.LieType.SeitzGeneration.OuterHeisCoreProof

public section

namespace CFSG.LieType.SeitzGeneration


theorem seitzOuterLowNarrow_of_pairs' (hSL : SubfieldPairSLLt) (hSp : SubfieldPairSpOdd)
    (hSU : SubfieldPairSUOdd) (hUH : UnitaryHeisCore) (hUOH : UnitaryOuterHeisCore)
    (hO : SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      IsOrthogonalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1)) : SeitzOuterLowNarrow :=
  seitzOuterLowNarrow_of_pairs hSL hSp hSU outerHeisCore hUH hUOH hO

theorem innerEx_lowN_of_frontier (hUH : UnitaryHeisCore) (hUOH : UnitaryOuterHeisCore)
    (hSL : SubfieldPairSLLt) (hSp : SubfieldPairSpOdd) (hSU : SubfieldPairSUOdd)
    (hO : SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      IsOrthogonalIndex d.1 ∧ ¬ (p = 3 ∧ IsDFourIndex d.1))
    (hPar : SeitzExcParabolic) (hParEx : ExcParabolicPlane) (hAni : SeitzExcAnisotropic)
    (hXON : SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧
      (¬ IsClassicalIndex d.1 ∨ (p = 3 ∧ IsDFourIndex d.1))) :
    KFactSeitzRankTwoInnerEx ∧ KFactSeitzRankTwoLowN :=
  innerEx_lowN_of_heisCore hUH (seitzOuterLowNarrow_of_pairs' hSL hSp hSU hUH hUOH hO) hPar
    hParEx hAni hXON

end CFSG.LieType.SeitzGeneration
