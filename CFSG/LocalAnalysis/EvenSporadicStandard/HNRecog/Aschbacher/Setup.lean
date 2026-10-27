module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.LeCommutator
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.IndexCommutator
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.CentralizerCommutator

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

theorem AschbacherHyp.index_commutator [Finite C] (hC : AschbacherHyp C Q) :
    (commutator C).index = 2 :=
  hC.index_commutator_of_le_commutator hC.le_commutator

theorem AschbacherHyp.centralizer_commutator_le [Finite C] (hC : AschbacherHyp C Q) :
    centralizer (commutator C : Set C) ≤ centerOf Q :=
  hC.centralizer_commutator_le_of_le_commutator hC.le_commutator

end CFSG.EvenSporadicStandard.HNRecog
