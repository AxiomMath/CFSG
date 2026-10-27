module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec7l77_B_le_L [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) : B ≤ L :=
  hc.normalE16.1.trans inf_le_right

theorem sec7l77_B_le_S [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) : B ≤ S :=
  hc.normalE16.1.trans inf_le_left

theorem sec7l77_B_le_A [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) : B ≤ ASub S B := by
  intro x hx
  refine Subgroup.subset_closure ⟨⟨sec7l77_B_le_S hc hx, ?_⟩, hc.normalE16.2.1.1.2 x hx⟩
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  exact congrArg Subtype.val (hc.normalE16.2.1.1.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)

theorem sec7l77_A_inf_L [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hc : Sec7Choice G t L S z g B) :
    ASub S B ⊓ L = B := by
  have hctx := hc.ctx
  refine le_antisymm ?_ (le_inf (sec7l77_B_le_A hc) (sec7l77_B_le_L hc))
  rintro x ⟨hxA, hxL⟩
  have hA : ASub S B ≤ S ⊓ centralizer (B : Set G) :=
    (Subgroup.closure_le _).mpr fun y hy => hy.1
  have hCB : L ⊓ centralizer (B : Set G) = B :=
    (hP.aut_B G L hctx.isOm6P (S ⊓ L) (hctx.isSylow2Of_inf h36) B hc.normalE16).2.1
  rw [← hCB]
  exact ⟨hxL, (hA hxA).2⟩

end CFSG.OddStandard.SmallF3.Omega
