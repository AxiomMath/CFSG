module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

theorem mul_self_of_isElemAbelian_two {G : Type*} [Group G] {E : Subgroup G}
    (h : IsElemAbelian 2 E) {g : G} (hg : g ∈ E) : g * g = 1 :=
  CFSG.Open.IsElemAbelian.mul_self_eq_one h hg

variable {F : Type} [Field F] [CharP F 2]

end CFSG.OddStandard.Seitz77
