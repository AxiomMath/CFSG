module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266UMultHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.MultA3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1 CFSG.LocalAnalysis.GLTheoremA.CatB.MultA2

section Holds


theorem multAlphaAt_of_X (G : Type) [Group G] [Finite G] (hX : MultAG2Residual G) :
    MultAlphaAt G := by
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  refine ⟨?_, ?_, T266.multAU6CoreChev_holds⟩
  · intro X L b n hL hLq hbp hR hI hcat
    have hIne : Ipart 3 L b ≠ ⊥ := glaPComponent_ne_bot' hI
    have hE : ∃ E : Subgroup (PSimple 3 L), IsSimpleGroup ↥E ∧ chevTransfer 3 L (Ipart 3 L b) = E := by
      rcases hR with hF | ⟨-, hT, hNI⟩
      · exact image_simple_fieldOn FR.Res.smallDatum_holds
          (FR.Res.twF4Core_holds Nat.prime_three (by norm_num)) hF hbp hIne
      · exact image_simple_td4 FR.Res.td4Core_holds hL (hX.1 X L b n hL hLq hbp hT hNI hI hcat) hT hNI hbp hIne
    obtain ⟨hsub, hn⟩ := layer_wrapper hGA hL hLq inf_le_left hI hcat hE
    refine ⟨?_, center_pQuot_eq_bot_G2 hGA hI hcat⟩
    by_cases hn2 : n = 2
    · exact le_bot_iff.1 (hsub.trans (hX.2 X L b n hL hLq hbp hR hI hcat hn2).le)
    · exact hn hn2
  · intro X K n _ _ _ _
    exact u6_card_center K

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB.MultA3

end
