module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FF4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent (coreAt)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2 (imgX)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin (TwinT4Hyp)

section Final


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem fBase_quat (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) {b : Y} (hbS : b ∈ (S₁ : Subgroup Y)) (hF₁ : IsFAut R₁ b) :
    ∃ Q : Subgroup Y, IsSylow2In Q (coreAt b (tightCore R)) ∧
      Nonempty (↥Q ≃* QuaternionGroup (2 ^ (r - 1 - 2))) := by
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hR₁ : IsSylow2In R₁ (tightCore R) :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have h2 : IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hP.core.datum.twoGroup
  obtain ⟨Q, hQ, hqQ, hcard⟩ := isSylow2In_coreAt_of_isFAut hR₁ h2
    (mem_normalizer_core_of_isFAut hr hP hyp hbS hF₁) hF₁
  refine ⟨Q, hQ, ?_⟩
  obtain ⟨k, hk, hQc⟩ := hqQ.natCard_eq
  obtain ⟨k', hk', ⟨e⟩⟩ := hqQ
  rw [card_R₁ hr hP hyp] at hcard
  have h1 : 2 ^ (k + 3) = 2 ^ r := by
    rw [pow_succ, ← hQc]
    exact hcard
  have h3 : k + 3 = r := Nat.pow_right_injective (le_refl 2) h1
  have h4 : 2 ^ k' = 2 ^ k := by
    haveI : NeZero (2 ^ k') := ⟨by positivity⟩
    have hc := Nat.card_congr e.toEquiv
    rw [hQc, Nat.card_eq_fintype_card, QuaternionGroup.card] at hc
    have h5 : 2 ^ (k + 2) = 2 ^ (k' + 2) := by rw [hc]; ring
    have h6 := Nat.pow_right_injective (le_refl 2) h5
    rw [show k = k' by omega]
  have h7 : r - 1 - 2 = k := by omega
  rw [h7, ← h4]
  exact ⟨e⟩

end Final

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
