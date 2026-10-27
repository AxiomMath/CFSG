module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.GH74.GLS.Bg

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem pRank_subgroup_eq_open (p : ℕ) (H : Subgroup G) :
    CFSG.pRank p ↥H = CFSG.Open.pRank p H := CFSG.SectionRank.pRank_coe_eq_openPRank p H

theorem pRank_subgroup_mono (hp : 1 < p) {H K : Subgroup G} (h : H ≤ K) :
    CFSG.pRank p ↥H ≤ CFSG.pRank p ↥K := by
  rw [pRank_subgroup_eq_open, pRank_subgroup_eq_open]
  exact CFSG.SectionRank.pRank_mono hp h

theorem pRank_subgroup_le (hp : 1 < p) (H : Subgroup G) : CFSG.pRank p ↥H ≤ CFSG.pRank p G := by
  rw [pRank_subgroup_eq_open, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_mono hp le_top

theorem pRank_mulEquiv {G' : Type*} [Group G'] [Finite G'] (hp : 1 < p) (e : G ≃* G') :
    CFSG.pRank p G = CFSG.pRank p G' := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp e

end CFSG.GH74.GLS.Bg
