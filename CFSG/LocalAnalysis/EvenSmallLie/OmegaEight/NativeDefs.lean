module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting

public section

namespace CFSG.EvenSmallLie.OmegaEight

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

@[expose] def InvolutionsInOddPart (X : Type*) [Group X] : Prop :=
  ∀ u : X, orderOf u = 2 → u ∈ closure {g : X | g * u = u * g ∧ Odd (orderOf g)}

theorem InvolutionsInOddPart.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : InvolutionsInOddPart X) : InvolutionsInOddPart Y := by
  intro u hu
  have hu' : orderOf (e.symm u) = 2 := by rw [MulEquiv.orderOf_eq, hu]
  have hmem := h _ hu'
  have himg : (closure {g : X | g * e.symm u = e.symm u * g ∧ Odd (orderOf g)}).map
      e.toMonoidHom ≤ closure {g : Y | g * u = u * g ∧ Odd (orderOf g)} := by
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, ⟨hg, hodd⟩, rfl⟩
    refine subset_closure ⟨?_, by rwa [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]⟩
    have := congrArg e hg
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  simpa using himg ⟨_, hmem, rfl⟩

@[expose] noncomputable def mulEquivQuotientCenter {L : Type*} [Group L] (h : center L = ⊥) :
    L ⧸ center L ≃* L :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

end CFSG.EvenSmallLie.OmegaEight
