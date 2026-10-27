module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Prod
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Swap

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

theorem swapData_equiv_S₂ {K : Type*} [Group K] {z : K} {B S₁ S₂ : Subgroup K}
    (hs : SwapData K z B S₁ S₂) : Nonempty (↥S₁ ≃* ↥S₂) := by
  refine ⟨(Subgroup.equivMapOfInjective S₁ (MulAut.conj z).toMonoidHom
    (MulAut.conj z).injective).trans (MulEquiv.subgroupCongr hs.conj_eq.symm)⟩

theorem swapData_layer_equiv {K : Type*} [Group K] [Finite K] {z : K} {B S₁ S₂ : Subgroup K}
    (h : Setting K z B) (hs : SwapData K z B S₁ S₂) :
    Nonempty (↥(layer K) ≃* ↥S₁ × ↥S₁) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_sup_prod hs.commute (hs.disjoint h)
  exact ⟨(MulEquiv.subgroupCongr hs.layer_eq).trans
    (e.trans (MulEquiv.prodCongr (MulEquiv.refl ↥S₁) (swapData_equiv_S₂ hs).some.symm))⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent
