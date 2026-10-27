module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameCore
public import CFSG.ClassicalInvolution.Q3.Q3T6DStmt
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

section Lemmas

variable {G : Type} [Group G]

theorem conjSub_sec20O2_le {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    conjSub g (sec20O2 X) ≤ sec20O2 X := by
  unfold conjSub
  rw [Subgroup.map_le_iff_le_comap, sec20O2, Subgroup.closure_le]
  rintro x ⟨hxX, hxo⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  apply Subgroup.subset_closure
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxX, ?_⟩
  have := (MulAut.conj g).orderOf_eq x
  rw [MulAut.conj_apply] at this
  rw [this]
  exact hxo

end Lemmas

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
