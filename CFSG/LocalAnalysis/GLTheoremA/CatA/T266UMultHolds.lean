module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266UMult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.CatB.MultA1 CFSG.LocalAnalysis.GLTheoremA.CatB.MultA2
open CFSG.LocalAnalysis.GLTheoremA.CatB.MultA3 CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1
open scoped commutatorElement

section Holds

variable {G : Type} [Group G] [Finite G]

theorem multAU6CoreChev_holds :
    ∀ (X L : Subgroup G) (b : G) (n : ℕ), GLAPComponent 3 X L → CFSG.Open.IsQuasisimple ↥L → b ^ 3 = 1 →
      IsChevSimple 2 (PSimple 3 L) →
      R2Prop 3 b L → GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) → Odd n → 1 < n →
      catalogIs (PSimple 3 (Ipart 3 L b)) (S10.isU6n n) → GLAPPrimeCoreOf 3 (Ipart 3 L b) = ⊥ := by
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  intro X L b n hL hLq hbp hchev hR hI _hodd hn1 hcat
  have hIne : Ipart 3 L b ≠ ⊥ := glaPComponent_ne_bot' hI
  have hE : ∃ E : Subgroup (PSimple 3 L), IsSimpleGroup ↥E ∧ chevTransfer 3 L (Ipart 3 L b) = E := by
    rcases hR with hF | ⟨-, hT, hNI⟩
    · exact image_simple_fieldOn FR.Res.smallDatum_holds
        (FR.Res.twF4Core_holds Nat.prime_three (by norm_num)) hF hbp hIne
    · exact image_simple_td4 FR.Res.td4Core_holds hL hchev hT hNI hbp hIne
  exact layer_core_eq_bot_u6 hGA hn1 hL hLq inf_le_left hI hcat hE

end Holds

end CFSG.LocalAnalysis.GLTheoremA.T266

end
