module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Main
public import CFSG.GH74.Uniqueness.SU.KI6QPCC
public import CFSG.GH74.Uniqueness.SU.KI6Z4

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open CFSG.ProperTwoGeneratedCore.Lemma37

theorem canonicalStatement_all
    (G : Type) [Group G] [Finite G] : CanonicalStatement G :=
  fun hs hn S hr hc => by
    haveI := hs
    exact aschbacher_proper_two_generated_core G hn S hr hc

theorem quasisimpleQuaternionCoreClassification_all
    : QuasisimpleQuaternionCoreClassification :=
  fun J _ _ => quasisimpleQuaternionCoreClassificationBelow J fun K _ _ _ => canonicalStatement_all K

theorem quasisimpleProperCoreClassification_all
    : QuasisimpleProperCoreClassification :=
  qpcc_of_quaternion_canonical quasisimpleQuaternionCoreClassification_all canonicalStatement_all

theorem ki6 :
    K.KI6 :=
  ki6_of_QPCC' quasisimpleProperCoreClassification_all

end CFSG.GH74.Uniqueness.SU.K.R6
