module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Prelude
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf9Disc

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


section Wire

theorem twinConnInputsV₃_of_thm4 {n : ℕ} (h4 : Thm4RTwinBelow 3 n) : TwinConnInputsV₃ n :=
  ⟨fun Y _ _ R S t h => uPairSec_proved Y R S t h, h4⟩

theorem twinDiscBaseV₃_proved {n : ℕ} : TwinDisc.TwinDiscBaseV₃ n :=
  fun Y _ _ R S t h _ => uPairSec_proved Y R S t h

end Wire

section HasLifts

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem oddCent_bot_of_hasLifts {n : ℕ} (hcit : CIT3Below n) (hΦ : HypOmegaGen Φ)
    (hlt : Nat.card X < n) (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hl : HasLifts Φ) (hne : Φ.Nonempty) (z : X) (hz : z * z = 1) :
    oddCoreIn (Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  have hΩ := hypOmegaModU_liftFam hΦ.conjInvariant
  have hneL : (liftFam Φ).Nonempty := by
    obtain ⟨J, hJ⟩ := hne
    obtain ⟨L, u, hL⟩ := hl J hJ
    exact ⟨_, satU_mem_liftFam hJ hL⟩
  obtain ⟨D⟩ := exists_omegaLieU (p := 3) (f := 1)
    ((Uniform.citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr hcit) hΩ hneL hO hlt
  have hgen' : omegaGen (liftFam Φ) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    unfold omegaGen
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨L, u, hL⟩ := hl J hJ
    exact hL.le_sat.trans (le_omegaGen (satU_mem_liftFam hJ hL))
  exact oddCent_bot_of_lieSystemData3 (D.toLieSystemData3 hgen') hO z hz

end HasLifts

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10
