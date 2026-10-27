module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreRestr
public import CFSG.ClassicalInvolution.Asc77.AscIHSectF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdentLie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


section Lie

theorem oddCent_bot_of_lieSystemData3 {ι X : Type} [Finite ι] [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (D : LieSystemData3 ι X Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (x : X) (hx : x * x = 1) :
    oddCoreIn (Subgroup.centralizer ({x} : Set X)) = ⊥ := by
  have hS : (oddCoreIn (⊤ : Subgroup X)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_oddCoreIn ⊤))
  have h2 := CFSG.ComponentClassification.OddCore.maximal X (oddCoreIn ⊤) hS
    (odd_card_oddCoreIn _)
  have hO' : oddCoreIn (⊤ : Subgroup X) = ⊥ := by
    have hcf : componentClassificationOddCore X = ⊥ := hO
    rw [hcf] at h2
    exact le_bot_iff.mp h2
  exact oddCoreIn_centralizer_eq_bot_of_lieSystemData3
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero modelOddCentralizerFree3_proved
    m11Facts m11OddCentralizerFree D hO' x hx

theorem oddCent_bot_of_liftFam' {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}
    (hcit : CIT3Below n) (hΦ : HypOmegaGen Φ) (hlt : Nat.card X < n)
    (hO : classicalInvolutionOddCore X = ⊥) (hne : (liftFam Φ).Nonempty) {Y' : Subgroup X}
    (hY : Y' = omegaGen (liftFam Φ)) (a : ↥Y') (ha : a * a = 1) :
    oddCoreIn (Subgroup.centralizer ({a} : Set ↥Y')) = ⊥ := by
  haveI : Y'.Normal := hY ▸ omegaGen_normal (conjInvariant_liftFam hΦ.conjInvariant)
  have hΩ := hypOmegaModU_liftFam hΦ.conjInvariant
  have hΛ := Q3T6.hypOmegaModU_restrict hΩ Y'
  have hOZ : classicalInvolutionOddCore ↥Y' = ⊥ := oddCore_normal_eq_bot Y' hO
  have hltZ : Nat.card ↥Y' < n := lt_of_le_of_lt (Subgroup.card_le_card_group Y') hlt
  have hneZ : (restrictFamily (liftFam Φ) Y').Nonempty := by
    obtain ⟨M, hM⟩ := hne
    exact ⟨M.subgroupOf Y', M, hM, hY ▸ le_omegaGen hM, rfl⟩
  obtain ⟨D⟩ := exists_omegaLieU (p := 3) (f := 1)
    ((Uniform.citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr hcit) hΛ hneZ hOZ hltZ
  have hgen : omegaGen (restrictFamily (liftFam Φ) Y') = ⊤ :=
    omegaGen_restrictFamily_eq_top (liftFam Φ) Y' hY.symm
  exact oddCent_bot_of_lieSystemData3 (D.toLieSystemData3 hgen) hOZ a ha

end Lie

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10
