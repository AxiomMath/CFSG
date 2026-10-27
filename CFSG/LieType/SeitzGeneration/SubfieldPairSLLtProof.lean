module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSLTwo
public import CFSG.LieType.SeitzGeneration.SubfieldPairSLOdd
public import CFSG.LieType.SeitzGeneration.OuterLinearPlane

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

theorem three_le_card_of_not_charP_two {K : Type} [Field K] [Finite K] {k : Subfield K}
    (h : ¬ CharP K 2) : 3 ≤ Nat.card k := by
  by_contra hlt
  have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
  have heq : Nat.card k = 2 := by omega
  have h0 : Nat.card k • (1 : k) = 0 := card_nsmul_eq_zero'
  rw [heq] at h0
  have h0' : (2 : K) = 0 := by
    have := congrArg k.subtype h0
    rw [map_nsmul, map_one, map_zero] at this
    simpa using this
  exact h (CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h0')

theorem subfieldPairSLLt : SubfieldPairSLLt := by
  intro K _ _ k p hp hK n hn3 hnp A hne
  have hp2 : p ≠ 2 := by omega
  by_cases h2 : CharP K 2
  · exact subfieldPairSL_two k hp hK hn3 hnp A hne
  · exact subfieldPairSL_odd hp hp2 hK (three_le_card_of_not_charP_two h2) hn3 A hne

end CFSG.LieType.SeitzGeneration
