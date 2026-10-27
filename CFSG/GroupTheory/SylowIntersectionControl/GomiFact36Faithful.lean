module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSp4
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36FaithfulA6
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36FaithfulCount
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36FaithfulLie
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36FaithfulSection
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefOffender
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefSetup
import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSec
import CFSG.Quasithin.Background.GoldschmidtB69DeepSec

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.QuasithinUnique.Lin2

theorem gomiFact36Faithful_of (hN : GomiFact36Identification) (hSp : Sp4OddMultiplierTrivial) :
    GomiFact36Faithful := by
  intro W _ _ hW Y S L A h hAS hAL hAe hAq hAnc hcost I Z hIV hAI hAZ hIZ
  by_contra hC
  have hChev : IsGomiChevTwo ↥L := h.2.2.2.2.2.1
  have hLI : L ≤ stabSub I := hIZ.le_stabSub_left
  have hLZ : L ≤ stabSub Z := hIZ.le_stabSub_right
  have hV₀ : G6.submoduleClosure L (fixV S) ≤
      fixV (A ⊓ Subgroup.centralizer (L : Set (MulAut W))) :=
    submoduleClosure_fixV_le_fixV (inf_le_left.trans hAS) inf_le_right
  obtain ⟨hnt, he, hq, hoff⟩ := autSec_offender_facts hChev.1 hAL hAe hAq hAnc hcost hV₀ hLI hLZ
    hAI hAZ hIV hIZ.2.2.2
  have hodd := odd_card_inf_centSec hChev hIZ
  have h4 := GomiFact36Hyp.four_mul_card_sec_le hW h hAS hAL hAe hAnc hcost hIV hAI hAZ hIZ hC
  have hirr : XMod.IsIrrSec ↥(autSec L I Z) (⊥ : Subgroup (Sec I Z)) ⊤ :=
    (isGomiNoncentralFactor_autSec hIZ).2.2.1
  have hAL' := CFSG.LocalAnalysis.RankThreeUC.autSec_normalizes hAL ⟨hLI, hAI⟩ ⟨hLZ, hAZ⟩
  have hA' : autSec A I Z ≠ ⊥ := B69.autSec_ne_bot hAI hAZ hnt
  have hW' := sq_eq_one_sec hW I Z
  rcases isGomiNatural_autSec hN hW hChev h.2.2.2.2.2.2 hAL hAI hAZ hIZ hnt he hq hoff with
    ⟨a, -, hnat⟩ | ⟨a, ha, hnat⟩ | hnat | hnat
  · exact hC (inf_centSec_eq_bot_of_binaryNaturalSL hChev.1 hIZ hodd hnat)
  · exact hC (inf_centSec_eq_bot_of_binaryNaturalSp4 hSp hChev.1 hIZ hodd ha hnat)
  · have := card_mul_card_fixV_lt_of_alternatingNatural hW' hirr hAL' he hA' hnat
    omega
  · have := card_mul_card_fixV_lt_of_tripleA6Six hW' hirr hAL' he hA' hnat
    omega

end CFSG.GroupTheory
