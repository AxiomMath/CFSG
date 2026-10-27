module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf182
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Orbit


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {W H : Subgroup G}

theorem habel_of_WSet (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) :
    ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, hη, hWη⟩ := hW
  obtain ⟨S₁, hS₁, hinv⟩ := hη
  have := etaAbelian_of_gen hΩ S₁ η hS₁ hinv
  rwa [← hWη] at this

theorem mem_dstarComp_of_inf_W (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω) {M : Subgroup G}
    (hK : K ∈ Ω) (hM : M ∈ Ω) (hKW : K ⊓ W ∈ USet Ω) (hMW : M ⊓ W ∈ USet Ω) :
    M ∈ dstarComp Ω K :=
  mem_dstarComp_of_mem_USet_le_W hΩ hK hM hKW inf_le_left inf_le_right hMW inf_le_left inf_le_right
    (habel_of_WSet hΩ hW)

theorem centAll_of_centAllK (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hW : W ∈ WSet Ω)
    (hKW : K ⊓ W ∈ USet Ω) (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J)
    (hcent : ∀ x ∈ H, K ⊓ conjSub x W ∈ USet Ω →
      TwinDisc.CentralizersPrinted Ω K (conjSub x W) H) : CentAll Ω W H := by
  intro M hM hMW
  obtain ⟨h, hhH, rfl⟩ := htrans M (mem_dstarComp_of_inf_W hΩ hW hK hM hKW hMW)
  have hU : K ⊓ conjSub h⁻¹ W ∈ USet Ω := by
    have := USet.conj hΩ.conjInvariant hMW h⁻¹
    rwa [conjSub_inf', conjSub_inv_conjSub] at this
  have := (hcent h⁻¹ (H.inv_mem hhH) hU).conj hΩ.conjInvariant h
  rwa [conjSub_conjSub_inv, conjSub_eq_self_of_mem hhH] at this

end Orbit

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
