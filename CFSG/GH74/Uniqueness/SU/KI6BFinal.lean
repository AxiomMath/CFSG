module

public import CFSG.GH74.Uniqueness.SU.KI6BMain
public import CFSG.GH74.Uniqueness.SU.KI6BStrong
public import CFSG.GH74.Uniqueness.SU.KI6BNoOuter
public import CFSG.GH74.Uniqueness.SU.KI6BA5
public import CFSG.GH74.Uniqueness.SU.KI6Final

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

theorem ki6BFacts :
    KI6BFacts where
  rankOne := rankOne_facts
  noOuter := noOuterFourGroup rankOne_facts
  stronglyEmbedded := rankOne_stronglyEmbedded rankOne_facts
  sl25 := rankOne_sl25
  generation := a5CoverGeneration
  centralizer := a5CoverCentralizer

theorem ki6B :
    KI6B := ki6B_of_facts ki6BFacts

theorem ki6_of_KI6A
    (hA : KI6A) : K.KI6 := ki6_of_KI6A_KI6B hA ki6B

theorem ki6_of_QPCC
    (hQ : CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleProperCoreClassification)
    (hZ4 : KI6Z4) (hA9 : KI6TwoA9) : K.KI6 :=
  ki6_of_KI6A (ki6A_of hQ hZ4 hA9)

end CFSG.GH74.Uniqueness.SU.K.R6
