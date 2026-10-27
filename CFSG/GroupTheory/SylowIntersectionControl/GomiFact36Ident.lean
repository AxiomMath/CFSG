module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefInputs
public import CFSG.Quasithin.Background.B4HypCore
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.Quasithin.Background.C124FStar
import CFSG.Quasithin.Background.GoldschmidtB69DeepLt
import CFSG.Quasithin.Background.GoldschmidtB69DeepSec
import CFSG.Quasithin.MS93.S32U
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin

@[expose] def GomiB42CoreNatural : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4HypCore G L → IsGomiChevTwo ↥L →
      (IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L)) →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender G A → IsGomiNatural L ⊤ ⊥

theorem autSec_le_normalizer {W : Type} [CommGroup W] {L A : Subgroup (MulAut W)}
    {I Z : Subgroup W} (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z) :
    autSec A I Z ≤ Subgroup.normalizer (autSec L I Z : Set (MulAut (Sec I Z))) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha l hl
  exact B69.autSec_sup_conj hAL (sup_le hLI hAI) (sup_le hLZ hAZ)
    (autSec_mono le_sup_right I Z ha) hl

private theorem pCoreOf_sup_eq_bot_of_irr {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hIrr : XMod.IsIrrSec ↥(autSec L I Z) (⊥ : Subgroup (Sec I Z)) ⊤) :
    pCoreOf 2 (autSec L I Z ⊔ autSec A I Z) = ⊥ := by
  let G' := autSec L I Z ⊔ autSec A I Z
  change pCoreOf 2 G' = ⊥
  by_contra hbot
  have hNne : pCoreOf 2 G' ≠ ⊥ := hbot
  have hN2 : IsPGroup 2 ↥(pCoreOf 2 G') := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G'
  have hnt : Nontrivial (Sec I Z) := by
    obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt hIrr.1
    exact ⟨x, 1, fun h => hx (by simpa using h)⟩
  have hfixne : fixV (pCoreOf 2 G') ≠ ⊥ :=
    MS93.S32.fixV_ne_bot_of_isPGroup (sq_eq_one_sec hW I Z) hN2
  have hinv : XMod.IsInv ↥(autSec L I Z) (fixV (pCoreOf 2 G')) := by
    intro a l hl
    exact fixV_apply_mem_of_mem_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G' (Subgroup.mem_sup_left a.2)) hl
  have hfixtop : fixV (pCoreOf 2 G') ≠ ⊤ := by
    intro htop
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    apply MulEquiv.ext
    intro v
    have hv : v ∈ fixV (pCoreOf 2 G') := by rw [htop]; trivial
    exact hv n hn
  rcases hIrr.2 (fixV (pCoreOf 2 G')) hinv bot_le le_top with h | h
  · exact hfixne h
  · exact hfixtop h

theorem b4HypCore_autSec {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L A : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hA'el : IsElemAbelian2 (autSec A I Z))
    (hQS : CFSG.IsQuasisimple ↥(autSec L I Z))
    (hIrr : XMod.IsIrrSec ↥(autSec L I Z) (⊥ : Subgroup (Sec I Z)) ⊤) :
    B4HypCore (autSec L I Z ⊔ autSec A I Z) (autSec L I Z) := by
  have hA'norm : autSec A I Z ≤
      Subgroup.normalizer (autSec L I Z : Set (MulAut (Sec I Z))) :=
    autSec_le_normalizer hAL hLI hLZ hAI hAZ
  have hG'norm : autSec L I Z ⊔ autSec A I Z ≤
      Subgroup.normalizer (autSec L I Z : Set (MulAut (Sec I Z))) :=
    sup_le Subgroup.le_normalizer hA'norm
  have hO2 : pCoreOf 2 (autSec L I Z ⊔ autSec A I Z) = ⊥ :=
    pCoreOf_sup_eq_bot_of_irr hW hIrr
  have hn : ∀ y ∈ autSec L I Z ⊔ autSec A I Z, ∀ l ∈ autSec L I Z,
      y * l * y⁻¹ ∈ autSec L I Z :=
    fun y hy l hl => (Subgroup.le_normalizer_iff.mp hG'norm) y hy l hl
  have h2 : ∀ y ∈ autSec L I Z ⊔ autSec A I Z, ∃ k : ℕ, y ^ 2 ^ k ∈ autSec L I Z := by
    intro y hy
    exact ⟨1, by simpa using B1Red.sq_mem_of_mem_sup hA'norm hA'el.2 y hy⟩
  have hF : quasithinGenFitting (autSec L I Z ⊔ autSec A I Z) = autSec L I Z :=
    C124.quasithinGenFitting_eq_of_two_group_quot le_sup_left hn
      (Or.inl (B1Red.isQuasisimple_to_open hQS)) h2 hO2
  exact ⟨hF.symm, hQS, hIrr⟩

private theorem isGomiNatural_of_autSec {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {I Z : Subgroup W} (hZI : Z ≤ I) (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hfaith : L ⊓ centSec I Z = ⊥) (h : IsGomiNatural (autSec L I Z) ⊤ ⊥) :
    IsGomiNatural L I Z := by
  rcases h with ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | h | h
  · exact Or.inl ⟨a, ha, B5.binaryNaturalSL_of_autSec hZI hLI hLZ hfaith h⟩
  · exact Or.inr (Or.inl ⟨a, ha, B5.binaryNaturalSp4_of_autSec hZI hLI hLZ hfaith h⟩)
  · exact Or.inr (Or.inr (Or.inl (B5.alternatingNatural_of_autSec hZI hLI hLZ hfaith h)))
  · exact Or.inr (Or.inr (Or.inr (B5.tripleA6Six_of_autSec hZI hLI hLZ hfaith h)))

theorem gomiFact36Identification_of_b42CoreNatural (h : GomiB42CoreNatural) :
    GomiFact36Identification := by
  intro W _ _ hW2 L A I Z hChev hLie hAL hAI hAZ hNF hfaith hAcent hAel _ hcost
  have hLI : L ≤ stabSub I :=
    B1.le_stabSub_of_invariant fun l hl w hw => hNF.1 ⟨l, hl⟩ w hw
  have hLZ : L ≤ stabSub Z :=
    B1.le_stabSub_of_invariant fun l hl w hw => hNF.2.1 ⟨l, hl⟩ w hw
  have hZlt : Z < I := hNF.2.2.1.1
  have hQS : CFSG.IsQuasisimple ↥(autSec L I Z) :=
    B5.isQuasisimple_autSec hLI hLZ hfaith hChev.1
  have hIrr : XMod.IsIrrSec ↥(autSec L I Z) (⊥ : Subgroup (Sec I Z)) ⊤ := by
    refine B5.isIrrSec_autSec hZlt ?_ hLI hLZ
    intro J hJ hZJ hJI
    exact hNF.2.2.1.2 J (fun a x hx => hJ a a.2 x hx) hZJ hJI
  have hB4 : B4HypCore (autSec L I Z ⊔ autSec A I Z) (autSec L I Z) :=
    b4HypCore_autSec hW2 hLI hLZ hAI hAZ hAL hAel hQS hIrr
  have hA'ne : autSec A I Z ≠ ⊥ := B69.autSec_ne_bot hAI hAZ hAcent
  have hFF : IsFFModule (autSec L I Z ⊔ autSec A I Z) :=
    ⟨autSec A I Z, le_sup_right, hA'ne, hAel, by simpa using hcost⟩
  obtain ⟨B, hB⟩ := B6.exists_isFFStarOffender hFF
  have hChev' : IsGomiChevTwo ↥(autSec L I Z) :=
    IsGomiChevTwo.of_mulEquiv (B5.secEquiv L hLI hLZ hfaith) hChev
  have hLie' : IsGomiL3 (↥(autSec L I Z) ⧸ Subgroup.center ↥(autSec L I Z)) ∨
      IsGomiSp4 (↥(autSec L I Z) ⧸ Subgroup.center ↥(autSec L I Z)) := by
    let eZ := QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(autSec L I Z))
      (B5.secEquiv L hLI hLZ hfaith) (Subgroup.map_center_eq (B5.secEquiv L hLI hLZ hfaith))
    exact hLie.imp (fun h3 => IsGomiL3.of_mulEquiv eZ h3)
      (fun h4 => IsGomiSp4.of_mulEquiv eZ h4)
  have hnat : IsGomiNatural (autSec L I Z) ⊤ ⊥ :=
    h (Sec I Z) (sq_eq_one_sec hW2 I Z) (autSec L I Z ⊔ autSec A I Z)
      (autSec L I Z) hB4 hChev' hLie' B hB
  exact isGomiNatural_of_autSec hZlt.le hLI hLZ hfaith hnat

end CFSG.GroupTheory
