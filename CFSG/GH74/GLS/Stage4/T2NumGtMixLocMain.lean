module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocCore
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocA
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocB
public import CFSG.GH74.GLS.Stage4.T2NumGtMixSecDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank

theorem ch6Mix_loc : Ch6MixLoc := by
  intro G _ _ _ Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem _ hmod
  have := hSet.finite₁
  have := hSet.finite₂
  have h4 : (q₁ % 4 = 1 ∧ q₂ % 4 = 3) ∨ (q₁ % 4 = 3 ∧ q₂ % 4 = 1) := by
    obtain ⟨k, hk⟩ := hSet.odd₁
    obtain ⟨l, hl⟩ := hSet.odd₂
    omega
  rcases h4 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨H, w₁, w₂, φ₁, φ₂, hcfg, -, hrange₁, hc₂⟩ := mixCfg_a hSet hRem ha hb
    obtain ⟨N, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ := loc5M_of_cfg hSet hcfg φ₁ hrange₁ φ₂ hc₂
    exact ⟨N, t, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩
  · obtain ⟨u, H, w₁, w₂, φ₁, φ₂, hcfg, -, hrange₁, hc₂⟩ := mixCfg_b hSet hRem ha hb
    obtain ⟨N, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ := loc5M_of_cfg hSet hcfg φ₁ hrange₁ φ₂ hc₂
    exact ⟨N, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩

end CFSG.GH74.GLS.Stage4.Rest
