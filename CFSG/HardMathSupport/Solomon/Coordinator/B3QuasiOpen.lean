module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporOpen
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieHolds

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census


theorem b3SporRestPair_of_high (hJ4 : J4ThreeCentralizerResidual)
    (hhigh : ∀ name p, B3SporRestPair name p → p ≠ 3 → B3SporPair name p) :
    ∀ name p, B3SporRestPair name p → B3SporPair name p := by
  intro name p h
  by_cases hp : p = 3
  · subst hp
    exact b3SporPair_rest_three CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds hJ4 name h
  · exact hhigh name p h hp

theorem b3Quasi_of_open
    (hBRc : BThreeFi23.BThreeRc) (hBRd : BThreeFi23.BThreeRd) (hB5A : BFiveNonCentral)
    (hM3K : TwoAPureKlein 3 CFSG.Monster.Generated.Gmat)
    (hM5K : TwoATwoCommuting 5 CFSG.Monster.Generated.Gmat)
    (hM7cl : MonsterSevenClasses CFSG.AGLEmbedding.Norton.MON5_7.dG
      CFSG.AGLEmbedding.Norton.MON5_7.zG)
    (hJ4 : J4ThreeCentralizerResidual)
    (hhigh : ∀ name p, B3SporRestPair name p → p ≠ 3 → B3SporPair name p)
    (hss : LieSemisimpleCent) (hout : LieDefCharOuter) : B3Quasi :=
  b3Quasi_of_b3Simple (b3Simple_of_families
    (b3SimpleSpor_of_open hBRc hBRd hB5A hM3K hM5K hM7cl (b3SporRestPair_of_high hJ4 hhigh))
    (b3SimpleLie_of_open hss hout) b3SimpleAlt_holds)

theorem input14_5Spor_of_open'
    (hBRc : BThreeFi23.BThreeRc) (hBRd : BThreeFi23.BThreeRd) (hB5A : BFiveNonCentral)
    (hM3K : TwoAPureKlein 3 CFSG.Monster.Generated.Gmat)
    (hM5K : TwoATwoCommuting 5 CFSG.Monster.Generated.Gmat)
    (hM7cl : MonsterSevenClasses CFSG.AGLEmbedding.Norton.MON5_7.dG
      CFSG.AGLEmbedding.Norton.MON5_7.zG)
    (hJ4 : J4ThreeCentralizerResidual)
    (hhigh : ∀ name p, B3SporRestPair name p → p ≠ 3 → B3SporPair name p) : Input14_5Spor :=
  input14_5Spor_of_open hBRc hBRd hB5A hM3K hM5K hM7cl (b3SporRestPair_of_high hJ4 hhigh)

end CFSG.HardMathSupport.Solomon.Coordinator
