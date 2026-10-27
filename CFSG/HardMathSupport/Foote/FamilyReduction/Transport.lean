module

public import CFSG.HardMathSupport.Foote.FamilyReduction.Abstract
public import CFSG.Sporadic.HeldB.FixedTransport
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.LU.Local.FiveSL2

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem Comp5.congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (h : Comp5 Q) :
    Comp5 Q' := by
  obtain ⟨α, hα, K, hK, ⟨eK⟩⟩ := h
  let f := CFSG.Sporadic.HeldB.fixedSubgroupCongr e α
  refine ⟨MulAut.congr e α, ?_, K.map f.toMonoidHom, ?_, ?_⟩
  · rw [CFSG.Sporadic.HeldB.orderOf_congr, hα]
  · exact CFSG.LocalCores.isComponent_map_mulEquiv f hK
  · exact ⟨(K.equivMapOfInjective f.toMonoidHom f.injective).symm.trans eK⟩

theorem not_isSimpleGroup_sl2_five {K : Type} [Group K]
    (e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ≃* K) : ¬ IsSimpleGroup K := by
  intro hs
  have hc := CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card e
  have h120 := CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · rw [h, Subgroup.card_bot] at hc
    omega
  · rw [h, Subgroup.card_top, h120] at hc
    omega

end CFSG.HardMathSupport.Foote.FamilyReduction
