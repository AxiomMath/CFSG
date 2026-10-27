module

public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem glaPLayer_fixSubgroup_congr {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} (hp : p.Prime) (e : G ≃* H) (α : MulAut G) :
    GLAPLayer p (fixSubgroup (MulAut.congr e α)) =
      (GLAPLayer p (fixSubgroup α)).map (e : G →* H) := by
  rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e α]
  exact (glaPLayer_map_eq_of_injective hp e.toMonoidHom e.injective _).symm

theorem glaPLayer_fixSubgroup_congr_ne_bot_iff {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] {p : ℕ} (hp : p.Prime) (e : G ≃* H) (α : MulAut G) :
    GLAPLayer p (fixSubgroup (MulAut.congr e α)) ≠ ⊥ ↔ GLAPLayer p (fixSubgroup α) ≠ ⊥ := by
  rw [glaPLayer_fixSubgroup_congr hp e α]
  exact not_iff_not.2 (Subgroup.map_eq_bot_iff_of_injective _ e.injective)

end CFSG

end
