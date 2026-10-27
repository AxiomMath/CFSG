module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUTheta
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUFin
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYKBar

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem fin76bS16KBar :
    Fin76bS16KBar := by
  unfold Fin76bS16KBar
  intro G _ _ L z t T E Q x B β h S hS2 hSC hSmax hzS hcard
  have c : OuterS16Ctx G L z t T E Q x B β S := ⟨h, hS2, hSC, hSmax, hzS, hcard⟩
  obtain ⟨θ⟩ := c.exists_theta
  obtain ⟨Em⟩ := exists_kemb h.outerB.beta_order θ (fun y hy htriv => h.ker_action hy htriv)
  have hDP : ∀ d ∈ L ⊓ centralizer ({β} : Set G), Em.f d ∈ CFSG.EvenSporadicStandard.M24Std.CU43.P :=
    fun d hd => Em.f_mem_P_of_A6 inf_le_right h.Dbar_iso hd
  obtain ⟨σ₀, v, ξ, hD0, -⟩ := h.exists_lData
  obtain ⟨e⟩ := c.S_dih Em hDP hD0
  exact ⟨⟨e⟩, fun σ v ξ hD s hs h8 => c.sigma_s Em e hD hs h8,
    fun σ v ξ hD s hs h8 h5 => c.zsigma Em hDP e hD hs h8 h5, c.K0_facts Em hD0 hDP⟩

end CFSG.EvenSporadicStandard.Fin76b
