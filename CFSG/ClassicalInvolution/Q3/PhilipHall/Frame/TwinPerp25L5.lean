module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25L3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

section Lie

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem layer_lifts (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hT : TwinThmE.T4Supply) (hno : SecNoExitAt Ω a) :
    HasLifts (TwinDisc.secFam Ω a) ∧ omegaGen (liftFam (TwinDisc.secFam Ω a)) = ⊤ ∧
      (∀ K₁ ∈ liftFam (TwinDisc.secFam Ω a), ∀ L₁ ∈ liftFam (TwinDisc.secFam Ω a),
        ∃ g : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a), conjSub g K₁ = L₁) ∧
      (TwinDisc.secFam Ω a).Nonempty := by
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  obtain ⟨hKtq, -, -, -, -, -⟩ := layer_twins_tq hyp hacA
  have hne : (TwinDisc.secFam Ω a).Nonempty := ⟨_, secImg_mem_secFam hKtq⟩
  obtain ⟨-, hl, -⟩ := lifts_of_noExit hih.2 hlt hS hno
  have hgen : omegaGen (liftFam (TwinDisc.secFam Ω a)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hS.gen]
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨L, u, hL⟩ := hl J hJ
    exact hL.le_sat.trans (le_omegaGen (satU_mem_liftFam hJ hL))
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨L₀, u₀, hL₀⟩ := hl K₀ hK₀
  have hM₀ := satU_mem_liftFam hK₀ hL₀
  have htr := layer_transitive hyp ha2 ha1 hacA hT hno
  have ht := liftFam_trans hS.hyp hM₀ hL₀.le_sat (fun J' hJ' => htr K₀ hK₀ J' hJ')
  refine ⟨hl, hgen, ?_, ⟨K₀, hK₀⟩⟩
  intro K₁ hK₁ L₁ hL₁
  obtain ⟨g₁, h₁⟩ := ht K₁ hK₁
  obtain ⟨g₂, h₂⟩ := ht L₁ hL₁
  exact ⟨g₂ * g₁⁻¹, by rw [conjSub_mul, ← h₁, conjSub_inv_conjSub, h₂]⟩

end Lie

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
