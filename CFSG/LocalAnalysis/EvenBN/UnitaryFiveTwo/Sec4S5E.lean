module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4R2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem t_comm_of_mem_S (h : d.Hyp) {s : G} (hs : s ∈ d.S) : d.t * s = s * d.t :=
  (mem_centralizer_singleton_iff.1 (h.R_le_H (mem_sup_left hs))).symm

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
