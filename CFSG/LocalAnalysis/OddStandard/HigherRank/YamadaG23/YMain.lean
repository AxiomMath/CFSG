module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YOutside
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec4S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec7S
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Setting3Ext
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.SetupExists

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

section Setup

theorem settingExists_of (hF : G23Facts) : SettingExists :=
  fun _ _ _ _ hS hL _ ht ht2 => Setup.exists_setting3 hF hS hL ht ht2

end Setup

theorem yamadaCase3Core_of_inputs (hSet : SettingExists) (h4 : Sec4False) (h5i : Sec5Intro)
    (h51 : Sec51) (h5 : Sec5) (h6 : Sec6) (h64 : Sec64) (h7 : Sec7False) (h6F : Y6F) :
    YamadaCase3Core := by
  intro G _ _ L hS hL
  obtain ⟨t, ht, ht2⟩ := Setup.exists_involution hS
  obtain ⟨s, -⟩ := hSet G L hS hL t ht ht2
  obtain ⟨e⟩ := Setting3.nonempty_ext hS s
  by_cases hA : BranchA e
  · exact (h4 G L hS hL s e hA).elim
  · obtain ⟨d, hd, hd2, hdn, hI⟩ := h5i G L hS hL s e hA
    let c0 : Ctx5pre G L := ⟨s, e, hA, d, hd, hd2, hdn, hI⟩
    have hg : ∃ g : G, s.R ≠ s.T →
        g ∈ s.T ∧ g ∉ s.R ∧ ActsAs L g s.fr'.σ ∧ g ^ 2 = 1 ∧ g * d * g⁻¹ = d := by
      by_cases hRT : s.R = s.T
      · exact ⟨1, fun h => (h hRT).elim⟩
      · obtain ⟨g, hgs⟩ := h51 G L hS hL c0 hRT
        exact ⟨g, fun _ => hgs⟩
    obtain ⟨g, hgs⟩ := hg
    let c5 : Ctx5 G L := { toCtx5pre := c0, g := g, g_spec := hgs }
    have hF5 : c5.Facts5 := h5 G L hS hL c5
    rcases hF5.2.2.2.2.2.2 with ⟨hV, -⟩ | ⟨hV, -⟩
    · exact (h7 G L hS hL ⟨c5, hV⟩ hF5).elim
    · let c6 : Ctx6 G L := { toCtx5 := c5, hV := hV }
      exact h6F G L hS hL c6 hF5 (h6 G L hS hL c6) (h64 G L hS hL c6)

end CFSG.OddStandard.HigherRank.YamadaG23
