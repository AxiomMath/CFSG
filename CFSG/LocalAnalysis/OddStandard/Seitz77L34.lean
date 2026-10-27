module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.OddStandard.Seitz77Setup

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem Hyp.commutator_eq_top (h : Hyp G A) : commutator ↥A = ⊤ := h.standard.1.1

theorem Hyp.nonempty_equiv_S (h : Hyp G A) :
    Nonempty (↥A ⧸ center ↥A ≃* PSL3Four.S) :=
  CatFactsSmall.nonempty_equiv_psl34_of_lieModel h.model

end CFSG.OddStandard.Seitz77
