module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverType

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Quasithin.SmithCurtis CoxeterSystem

section Cover

variable {Ĝ G : Type*} [Group Ĝ] [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
  [Group W] {cs : CoxeterSystem M W} {p : ℕ} [Finite Ĝ] [Fact p.Prime] {D : CurtisDatum G cs p}
  {π : Ĝ →* G} {C : CentralCoverData D π p} {F : B → Type} [∀ s, Field (F s)]
  {R : CoverRankOne C F} [Fintype B]

theorem ker_le_comap_H (z : Ĝ) (hz : z ∈ π.ker) : z ∈ D.H.comap π := by
  rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]
  exact one_mem _

end Cover

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
