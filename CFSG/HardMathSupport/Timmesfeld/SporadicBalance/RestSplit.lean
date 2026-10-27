module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNWitness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint

structure SporadicOneRestOPrime : Prop where
  Suz_three : SporadicOPrimeHolds .Suz 3
  ONan_three : SporadicOPrimeHolds .ONan 3
  Co3_three : SporadicOPrimeHolds .Co3 3
  Co2_three : SporadicOPrimeHolds .Co2 3
  Co1_three : SporadicOPrimeHolds .Co1 3
  Fi22_three : SporadicOPrimeHolds .Fi22 3
  Fi23_three : SporadicOPrimeHolds .Fi23 3
  Fi24Prime_three : SporadicOPrimeHolds .Fi24Prime 3
  Ly_three : SporadicOPrimeHolds .Ly 3
  Th_three : SporadicOPrimeHolds .Th 3
  B_three : SporadicOPrimeHolds .B 3
  M_three : SporadicOPrimeHolds .M 3
  Co1_five : SporadicOPrimeHolds .Co1 5
  HN_five : SporadicOPrimeHolds .HN 5
  Ly_five : SporadicOPrimeHolds .Ly 5
  B_five : SporadicOPrimeHolds .B 5
  M_five : SporadicOPrimeHolds .M 5
  M_seven : SporadicOPrimeHolds .M 7

structure SporadicOneRestOuter : Prop where
  Suz_three : SporadicOuterHolds .Suz 3
  ONan_three : SporadicOuterHolds .ONan 3
  Fi22_three : SporadicOuterHolds .Fi22 3
  Fi24Prime_three : SporadicOuterHolds .Fi24Prime 3
  HN_five : SporadicOuterHolds .HN 5

theorem sporadicOneRest_of_split
    (hO : SporadicOneRestOPrime) (hX : SporadicOneRestOuter) : SporadicOneRest where
  Suz_three := ⟨hO.Suz_three, hX.Suz_three⟩
  ONan_three := ⟨hO.ONan_three, hX.ONan_three⟩
  Co3_three := ⟨hO.Co3_three, sporadicOuterHolds_Co3 3⟩
  Co2_three := ⟨hO.Co2_three, sporadicOuterHolds_Co2 3⟩
  Co1_three := ⟨hO.Co1_three, sporadicOuterHolds_Co1 3⟩
  Fi22_three := ⟨hO.Fi22_three, hX.Fi22_three⟩
  Fi23_three := ⟨hO.Fi23_three, sporadicOuterHolds_Fi23 3⟩
  Fi24Prime_three := ⟨hO.Fi24Prime_three, hX.Fi24Prime_three⟩
  HN_three := sporadicOnePairHolds_HN_three
  Ly_three := ⟨hO.Ly_three, sporadicOuterHolds_Ly 3⟩
  Th_three := ⟨hO.Th_three, sporadicOuterHolds_Th 3⟩
  B_three := ⟨hO.B_three, sporadicOuterHolds_B 3⟩
  M_three := ⟨hO.M_three, sporadicOuterHolds_M 3⟩
  Co1_five := ⟨hO.Co1_five, sporadicOuterHolds_Co1 5⟩
  HN_five := ⟨hO.HN_five, hX.HN_five⟩
  Ly_five := ⟨hO.Ly_five, sporadicOuterHolds_Ly 5⟩
  B_five := ⟨hO.B_five, sporadicOuterHolds_B 5⟩
  M_five := ⟨hO.M_five, sporadicOuterHolds_M 5⟩
  M_seven := ⟨hO.M_seven, sporadicOuterHolds_M 7⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
