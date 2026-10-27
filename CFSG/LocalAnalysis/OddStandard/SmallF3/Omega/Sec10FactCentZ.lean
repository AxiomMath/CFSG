module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem asc82FactCentZ5_of_cert :
    Asc82FactCentZ5 := by
  intro G _ _ L hL z hz
  obtain ⟨F, hzL, hF⟩ := Pk.exists_frame_tA hL hz
  have hC : F.img (L ⊓ centralizer ({z} : Set G)) = Pk.Cs := by
    have h := F.img_inf_centralizer_singleton ⟨z, hzL⟩
    rw [hF] at h
    exact h
  rw [← F.card_img (X := L ⊓ centralizer ({z} : Set G)) inf_le_left, hC]
  exact Pk.card_Cs

end CFSG.OddStandard.SmallF3.Omega
