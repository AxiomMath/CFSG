module

public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotCongr
public import CFSG.ClassicalInvolution.Q3.TL4D4NCFam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

namespace TwinDisc

section Glue

variable {Y : Type} [Group Y] [Finite Y]

theorem centralizer_le_normalizer_alphaOf (A : Subgroup Y) :
    Subgroup.centralizer (A : Set Y) ≤ Subgroup.normalizer (alphaOf A : Set Y) := by
  intro g hg
  refine mem_normalizer_of_conjSub_eq ?_
  rw [← alphaOf_conjSub, conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hg)]

variable {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y} {K K' J W : Subgroup Y} {z u t : Y}

end Glue

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
