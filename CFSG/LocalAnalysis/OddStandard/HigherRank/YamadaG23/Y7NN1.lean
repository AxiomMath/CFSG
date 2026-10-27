module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NNa
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSt2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NAs6

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem sec7nt1_of (hB : Sec3Inputs) (h29 : Aut29Idx) : Sec7NT1 := by
  intro G _ _ L hS hL c h5 h7 hRT
  have hH : F33Hyp c.s c.e := f33hyp_of hB hS hL c.s c.e
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, h77⟩, h78⟩, _⟩ := id h7
  obtain ⟨L1, hL1⟩ : ∃ L1 : Subgroup G, IsCompPre c.s L1 := h77.2.resolve_right h78
  obtain ⟨P1, hsyl, hle⟩ := y7n_exists_P1 hH hRT h5 h7
  have hAbs := y7n_ntAbs_of_setting hB h29 hS hL c h5 h7 hRT hL1 hsyl hle
  exact ⟨L1, P1, normIn P1 ⁅L1, L1⁆, ⟨hL1, hsyl, hle, rfl, hAbs.normal, hAbs.split, hAbs.cases⟩⟩

end CFSG.OddStandard.HigherRank.YamadaG23
