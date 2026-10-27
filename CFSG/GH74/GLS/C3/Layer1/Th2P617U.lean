module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617G
public import CFSG.GH74.GLS.C3.Layer1.Th2P617Q
public import CFSG.GH74.GLS.C3.Layer1.Th2P617T

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2

theorem b_prop617_obs_gt4_proved
    (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) : B_prop617_obs_gt4 := by
  intro G _ _ hG x y K T S hs h7 hQ2 h4 B hB b J hobs _ hbx
  obtain ⟨y', T', S', hs', hcard, hrk, hB', hPb⟩ :=
    Th2.Obs.exists_adapted hL34 hG hs h7 hB hobs
  exact Th2.Obs.false_of_adapted hL34 h102 hG hs' h7 (hrk ▸ hQ2) (hcard ▸ h4) hB' hobs hbx hPb

end CFSG.GH74.GLS
