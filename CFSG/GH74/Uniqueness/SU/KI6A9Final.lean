module

public import CFSG.GH74.Uniqueness.SU.KI6A9
public import CFSG.GH74.Uniqueness.SU.KI6BFinal

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

theorem ki6TwoA9 : KI6TwoA9 := fun _ _ _ _ _ h _ hL hrank hA => h.ki6TwoA9 hL hrank hA

theorem ki6_of_QPCC_Z4
    (hQ : CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleProperCoreClassification)
    (hZ4 : KI6Z4) : K.KI6 :=
  ki6_of_QPCC hQ hZ4 ki6TwoA9

end CFSG.GH74.Uniqueness.SU.K.R6
