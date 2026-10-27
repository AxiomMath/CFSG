module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36FaithfulBasic
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefOffender
import CFSG.Quasithin.Background.F918P4
import CFSG.Quasithin.Background.GoldschmidtB69DeepSec
import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSec
import CFSG.Quasithin.Vol2.Ch10SecKIg
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefInputs
public import CFSG.Quasithin.Background.SmithB51LnSub

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem isGomiChevTwo_autSec [Finite W] {L : Subgroup (MulAut W)} (hL : IsGomiChevTwo ↥L)
    {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z) :
    IsGomiChevTwo ↥(autSec L I Z) := by
  have hLI : L ≤ stabSub I := hIZ.le_stabSub_left
  have hLZ : L ≤ stabSub Z := hIZ.le_stabSub_right
  let f := B5.Ln.secHomL L hLI hLZ
  have hf : Function.Surjective f := B5.Ln.secHomL_surjective hLI hLZ
  have hker : f.ker ≤ Subgroup.center ↥L := ker_secHomL_le_center hL.1 hIZ hLI hLZ
  have hQ : CFSG.IsQuasisimple ↥(autSec L I Z) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hL.1 f hf hker
  have hp : CFSG.pCore 2 ↥(autSec L I Z) = ⊥ := by
    let e : ↥L ⧸ f.ker ≃* ↥(autSec L I Z) :=
      QuotientGroup.quotientKerEquivOfSurjective f hf
    have hq : CFSG.pCore 2 (↥L ⧸ f.ker) = ⊥ := by
      simpa using CFSG.Quasithin.pCore_quotient_eq_bot f.ker hker (by simpa using hL.2.1)
    rw [← CFSG.pCore_map_iso 2 e, hq, Subgroup.map_bot]
  have hChev : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo
      (↥(autSec L I Z) ⧸ Subgroup.center ↥(autSec L I Z)) := by
    obtain ⟨eZ⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hL.1 f hf hker
    rcases hL.2.2 with ⟨d, hd, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨d, hd, ⟨φ⟩⟩
    · exact Or.inl ⟨d, hd, ⟨eZ.symm.trans φ⟩⟩
    · exact Or.inr (Or.inl ⟨n, hn, ⟨eZ.symm.trans φ⟩⟩)
    · exact Or.inr (Or.inr ⟨d, hd, ⟨eZ.symm.trans φ⟩⟩)
  exact ⟨hQ, hp, hChev⟩

theorem nonempty_quotient_center_autSec {L : Subgroup (MulAut W)} (hL : CFSG.IsQuasisimple ↥L)
    {I Z : Subgroup W} (hIZ : IsGomiNoncentralFactor L I Z) :
    Nonempty (↥(autSec L I Z) ⧸ Subgroup.center ↥(autSec L I Z) ≃* ↥L ⧸ Subgroup.center ↥L) := by
  have hLI : L ≤ stabSub I := hIZ.le_stabSub_left
  have hLZ : L ≤ stabSub Z := hIZ.le_stabSub_right
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hL
      (B5.Ln.secHomL L hLI hLZ) (B5.Ln.secHomL_surjective hLI hLZ)
      (ker_secHomL_le_center hL hIZ hLI hLZ)
  exact ⟨e.symm⟩

theorem isGomiNatural_autSec [Finite W] (hN : GomiFact36Identification)
    (hW : ∀ w : W, w ^ 2 = 1) {L A : Subgroup (MulAut W)} (hChev : IsGomiChevTwo ↥L)
    (hLie : IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L))
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) {I Z : Subgroup W}
    (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) (hIZ : IsGomiNoncentralFactor L I Z)
    (hnt : ¬ A ≤ centSec I Z) (he : IsElemAbelian2 (autSec A I Z))
    (hq : IsQuadratic (autSec A I Z))
    (hoff : Nat.card (Sec I Z) ≤ Nat.card ↥(autSec A I Z) * Nat.card ↥(fixV (autSec A I Z))) :
    IsGomiNatural (autSec L I Z) ⊤ ⊥ := by
  have hLI : L ≤ stabSub I := hIZ.le_stabSub_left
  have hLZ : L ≤ stabSub Z := hIZ.le_stabSub_right
  have hChev' : IsGomiChevTwo ↥(autSec L I Z) := isGomiChevTwo_autSec hChev hIZ
  have hLie' : IsGomiL3 (↥(autSec L I Z) ⧸ Subgroup.center ↥(autSec L I Z)) ∨
      IsGomiSp4 (↥(autSec L I Z) ⧸ Subgroup.center ↥(autSec L I Z)) := by
    obtain ⟨e⟩ := nonempty_quotient_center_autSec hChev.1 hIZ
    exact hLie.imp (fun h => IsGomiL3.of_mulEquiv e.symm h)
      (fun h => IsGomiSp4.of_mulEquiv e.symm h)
  have hcent : centSec (⊤ : Subgroup (Sec I Z)) ⊥ = ⊥ := eq_bot_iff.2 fun g hg =>
    Subgroup.mem_bot.2 (Vol2.Ch10.SecF.C10KH.eq_one_of_mem_centSec_top_bot hg)
  have hfaith : autSec L I Z ⊓ centSec (⊤ : Subgroup (Sec I Z)) ⊥ = ⊥ := by
    rw [hcent, inf_bot_eq]
  have hnt' : ¬ autSec A I Z ≤ centSec (⊤ : Subgroup (Sec I Z)) ⊥ := by
    intro hle
    have hbot : autSec A I Z = ⊥ := le_bot_iff.mp (by simpa [hcent] using hle)
    exact B69.autSec_ne_bot hAI hAZ hnt hbot
  have he' : IsElemAbelian2 (autSec (autSec A I Z) ⊤ ⊥) :=
    B69.isElemAbelian2_autSec (W := ⊤) (U := ⊥) he (fun _ _ _ => by simp)
      (B5.Ln.stabSub_bot_le _)
  have hq' : IsQuadratic (autSec (autSec A I Z) ⊤ ⊥) :=
    B69.isQuadratic_autSec (W := ⊤) (U := ⊥) (fun _ _ _ => by simp)
      (B5.Ln.stabSub_bot_le _) hq
  have hoff' : Nat.card (Sec (⊤ : Subgroup (Sec I Z)) ⊥) ≤
      Nat.card ↥(autSec (autSec A I Z) ⊤ ⊥) *
        Nat.card ↥(fixV (autSec (autSec A I Z) ⊤ ⊥)) := by
    refine card_sec_le_card_autSec_mul (I := ⊤) (Z := ⊥) (fun _ _ _ => by simp)
      (B5.Ln.stabSub_bot_le _) ?_ inf_le_right
    rw [Subgroup.card_top, hcent, inf_bot_eq, inf_top_eq]
    simpa using hoff
  exact hN (Sec I Z) (sq_eq_one_sec hW I Z) (autSec L I Z) (autSec A I Z) ⊤ ⊥ hChev' hLie'
    (CFSG.LocalAnalysis.RankThreeUC.autSec_normalizes hAL ⟨hLI, hAI⟩ ⟨hLZ, hAZ⟩)
    (fun _ _ _ => by simp) (B5.Ln.stabSub_bot_le _) (isGomiNoncentralFactor_autSec hIZ)
    hfaith hnt' he' hq' hoff'

end CFSG.GroupTheory
