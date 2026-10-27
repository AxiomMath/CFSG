module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3B

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem D₁_le_normalizer_Y (h : d.Hyp)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.D₁ ≤ normalizer (d.Y : Set G) := by
  have : d.D₃e₂ ⊔ d.M ≤ normalizer (d.Y : Set G) := sup_le
    (fun e he => mem_normalizer_of_forall_comm fun y hy =>
      (D₂_comm_Y' (h.D₃e₂_le_D₂ he) hy).symm) hKY
  exact h.D₁_eq_D₃e₂_sup_M.le.trans this

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
