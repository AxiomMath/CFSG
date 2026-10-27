module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefClifford
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefOffender
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36ChiefSetup
import CFSG.Quasithin.Background.GoldschmidtB69DeepSec
import CFSG.Quasithin.Background.SecIsoLChief
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

private abbrev centIn (A L : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  A ⊓ Subgroup.centralizer (L : Set (MulAut W))

private abbrev OffenderCost (A : Subgroup (MulAut W)) : Prop :=
  ∀ U : Subgroup W,
    Nat.card U * Nat.card ↥(A ⊓ centSec U ⊥) ≤ Nat.card A * Nat.card ↥(fixV A ⊓ U)

private abbrev FaithfulOn (L A : Subgroup (MulAut W)) (V₀ : Subgroup W) : Prop :=
  ∀ I Z : Subgroup W, I ≤ V₀ → A ≤ stabSub I → A ≤ stabSub Z → IsGomiNoncentralFactor L I Z →
    L ⊓ centSec I Z = ⊥

private theorem le_stabSub_of_isInv {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : XMod.IsInv ↥X U) : X ≤ stabSub U :=
  B1.le_stabSub_of_invariant fun x hx u hu => h ⟨x, hx⟩ u hu

private theorem isInv_of_le_stabSub {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : X ≤ stabSub U) : XMod.IsInv ↥X U :=
  fun x u hu => (mem_stabSub.1 (h x.2) u).2 hu

private theorem inf_centSec_eq {L A : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (hL : CFSG.IsQuasisimple ↥L)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hV₀fix : V₀ ≤ fixV (centIn A L))
    {I Z : Subgroup W} (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hIV : I ≤ V₀)
    (hnc : ¬ XMod.commOf ↥L I ≤ Z) :
    A ⊓ centSec I Z = centIn A L :=
  inf_centSec_eq_inf_centralizer hL hAL hLI hLZ hnc (hIV.trans hV₀fix)

private theorem isGomiNatural_of_ncf [Finite W] (hN : GomiFact36Identification)
    (hW : ∀ w : W, w ^ 2 = 1) {L A : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (hfaith : FaithfulOn L A V₀) (hChev : IsGomiChevTwo ↥L)
    (hLie : IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L))
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    (hAq : IsQuadratic A) (hAnc : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    (hcost : OffenderCost A) (hV₀fix : V₀ ≤ fixV (centIn A L)) {I Z : Subgroup W}
    (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hAI : A ≤ stabSub I) (hAZ : A ≤ stabSub Z)
    (hIV : I ≤ V₀) (hIZ : IsGomiNoncentralFactor L I Z) : IsGomiNatural L I Z := by
  have hnc : ¬ XMod.commOf ↥L I ≤ Z := hIZ.2.2.2
  obtain ⟨hnt, he, hq, hoff⟩ :=
    autSec_offender_facts hChev.1 hAL hAe hAq hAnc hcost hV₀fix hLI hLZ hAI hAZ hIV hnc
  exact hN W hW L A I Z hChev hLie hAL hAI hAZ hIZ (hfaith I Z hIV hAI hAZ hIZ) hnt he hq hoff

private theorem card_autSec_eq [Finite W] {L A : Subgroup (MulAut W)} {V₀ : Subgroup W}
    (hL : CFSG.IsQuasisimple ↥L)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hV₀fix : V₀ ≤ fixV (centIn A L))
    {I Z I' Z' : Subgroup W} (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (hAI : A ≤ stabSub I)
    (hAZ : A ≤ stabSub Z) (hIV : I ≤ V₀) (hnc : ¬ XMod.commOf ↥L I ≤ Z) (hLI' : L ≤ stabSub I')
    (hLZ' : L ≤ stabSub Z') (hAI' : A ≤ stabSub I') (hAZ' : A ≤ stabSub Z') (hIV' : I' ≤ V₀)
    (hnc' : ¬ XMod.commOf ↥L I' ≤ Z') :
    Nat.card (autSec A I Z) = Nat.card (autSec A I' Z') := by
  have h1 := card_autSec_mul hAI hAZ
  have h2 := card_autSec_mul hAI' hAZ'
  rw [inf_centSec_eq hL hAL hV₀fix hLI hLZ hIV hnc] at h1
  rw [inf_centSec_eq hL hAL hV₀fix hLI' hLZ' hIV' hnc'] at h2
  have hne : Nonempty ↥(centIn A L) := ⟨⟨1, (centIn A L).one_mem⟩⟩
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(centIn A L))) (h1.trans h2.symm)

private theorem isGomiNatural_of_secIsoL {L : Subgroup (MulAut W)} {I Z I' Z' : Subgroup W}
    (h : IsGomiNatural L I' Z') (hiso : SecIsoL L I Z I' Z') : IsGomiNatural L I Z := by
  have H : ∀ D : FFModel, D.Realizes L I' Z' → D.Realizes L I Z :=
    fun D hD => FFModel.Realizes.of_secIsoL hD hiso
  unfold IsGomiNatural BinaryNaturalSL BinaryNaturalSp4 TripleA6Six at h ⊢
  rcases h with ⟨a, ha, K, hfield, hfin, hcard, hR⟩ | ⟨a, ha, K, hfield, hfin, hcard, hR⟩ |
    hR | ⟨K, hfield, hfin, Γ₀, hcard, hdet, hhat, hcen, hR⟩
  · exact Or.inl ⟨a, ha, K, hfield, hfin, hcard, H _ hR⟩
  · exact Or.inr (Or.inl ⟨a, ha, K, hfield, hfin, hcard, H _ hR⟩)
  · exact Or.inr (Or.inr (Or.inl (H _ hR)))
  · exact Or.inr (Or.inr (Or.inr ⟨K, hfield, hfin, Γ₀, hcard, hdet, hhat, hcen, H _ hR⟩))

private def Good (L A : Subgroup (MulAut W)) (M : Subgroup W) : Prop :=
  (¬ ∃ I Z : Subgroup W, I ≤ M ∧ IsGomiNoncentralFactor L I Z) ∨
    ∃ I₀ Z₀ : Subgroup W, Z₀ ≤ I₀ ∧ I₀ ≤ M ∧ XMod.IsInv ↥L I₀ ∧ XMod.IsInv ↥L Z₀ ∧
      XMod.IsInv ↥A I₀ ∧ XMod.IsInv ↥A Z₀ ∧ IsGomiNoncentralFactor L I₀ Z₀ ∧
        ∀ I Z : Subgroup W, I ≤ M → IsGomiNoncentralFactor L I Z → SecIsoL L I Z I₀ Z₀

private theorem good_bot {L A : Subgroup (MulAut W)} : Good L A ⊥ := by
  refine Or.inl ?_
  rintro ⟨I, Z, hI, hIZ⟩
  obtain ⟨-, -, hirr, -⟩ := hIZ
  rw [le_bot_iff.1 hI] at hirr
  exact not_lt_of_ge bot_le hirr.1

private theorem isInv_of_isInv_sup {X Y : Subgroup (MulAut W)} {U : Subgroup W}
    (h : XMod.IsInv ↥(X ⊔ Y) U) : XMod.IsInv ↥X U ∧ XMod.IsInv ↥Y U :=
  ⟨fun x u hu => h ⟨(x : MulAut W), (le_sup_left : X ≤ X ⊔ Y) x.2⟩ u hu,
    fun y u hu => h ⟨(y : MulAut W), (le_sup_right : Y ≤ X ⊔ Y) y.2⟩ u hu⟩

private theorem exists_max_invariant_lt [Finite W] {L A : Subgroup (MulAut W)} {M : Subgroup W}
    (hM : M ≠ ⊥) :
    ∃ M' : Subgroup W, M' < M ∧ XMod.IsInv ↥L M' ∧ XMod.IsInv ↥A M' ∧
      ∀ N : Subgroup W, M' < N → N ≤ M → XMod.IsInv ↥L N → XMod.IsInv ↥A N → N = M := by
  have hfin : Finite (Subgroup W) :=
    Finite.of_injective (fun H : Subgroup W => (H : Set W)) SetLike.coe_injective
  obtain ⟨M', hM', hmax⟩ := WellFounded.has_min wellFounded_gt
    {M' : Subgroup W | M' < M ∧ XMod.IsInv ↥L M' ∧ XMod.IsInv ↥A M'}
    ⟨⊥, bot_lt_iff_ne_bot.2 hM, XMod.isInv_bot, XMod.isInv_bot⟩
  refine ⟨M', hM'.1, hM'.2.1, hM'.2.2, fun N hM'N hNle hNinvL hNinvA => ?_⟩
  by_contra hNne
  exact hmax N ⟨lt_of_le_of_ne hNle hNne, hNinvL, hNinvA⟩ hM'N

private theorem isIrrSec_sup_of_max {L A : Subgroup (MulAut W)} {M M' : Subgroup W}
    (hM'ltM : M' < M)
    (hmax : ∀ N : Subgroup W, M' < N → N ≤ M → XMod.IsInv ↥L N → XMod.IsInv ↥A N → N = M) :
    XMod.IsIrrSec ↥(L ⊔ A) M' M := by
  refine ⟨hM'ltM, fun J hJ hM'J hJle => ?_⟩
  by_cases hJM : J = M
  · exact Or.inr hJM
  · obtain ⟨hJinvL, hJinvA⟩ := isInv_of_isInv_sup hJ
    refine Or.inl (by_contra fun hne => hJM (hmax J ?_ hJle hJinvL hJinvA))
    exact lt_of_le_of_ne hM'J (Ne.symm hne)

private theorem isIrrSec_of_isIrrSec_sup_max [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L A : Subgroup (MulAut W)} {V₀ M M' : Subgroup W}
    (hChev : IsGomiChevTwo ↥L)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    (hAq : IsQuadratic A) (hcost : OffenderCost A) (hV₀fix : V₀ ≤ fixV (centIn A L))
    (hMV : M ≤ V₀) (hMinvL : XMod.IsInv ↥L M) (hM'invL : XMod.IsInv ↥L M')
    (hMinvA : XMod.IsInv ↥A M) (hM'invA : XMod.IsInv ↥A M')
    (hirr : XMod.IsIrrSec ↥(L ⊔ A) M' M) : XMod.IsIrrSec ↥L M' M := by
  have hLM : L ≤ stabSub M := le_stabSub_of_isInv hMinvL
  have hLM' : L ≤ stabSub M' := le_stabSub_of_isInv hM'invL
  have hAM : A ≤ stabSub M := le_stabSub_of_isInv hMinvA
  have hAM' : A ≤ stabSub M' := le_stabSub_of_isInv hM'invA
  have he : IsElemAbelian2 (autSec A M M') := B69.isElemAbelian2_autSec hAe hAM hAM'
  by_cases hc : XMod.commOf ↥L M ≤ M'
  · exact isIrrSec_of_isIrrSec_sup_of_commOf_le hW hLM hLM' hAM hAM' he hc hirr
  · refine isIrrSec_of_isIrrSec_sup hW hAL hLM hLM' hAM hAM' he
      (B69.isQuadratic_autSec hAM hAM' hAq) ?_ hirr
    have hker : A ⊓ centSec M M' ≤ centSec M ⊥ := by
      rw [inf_centSec_eq hChev.1 hAL hV₀fix hLM hLM' hMV hc]
      exact le_centSec_bot_of_le_fixV (hMV.trans hV₀fix)
    exact card_sec_le_card_autSec_mul hAM hAM' (hcost M) hker

private theorem isGomiNoncentralFactor_inf {L : Subgroup (MulAut W)} {M' I Z : Subgroup W}
    (hM' : XMod.IsInv ↥L M') (hIZ : IsGomiNoncentralFactor L I Z)
    (h : SecIsoL L I Z (I ⊓ M') (Z ⊓ M')) :
    IsGomiNoncentralFactor L (I ⊓ M') (Z ⊓ M') :=
  ⟨XMod.IsInv.inf hIZ.1 hM', XMod.IsInv.inf hIZ.2.1 hM', SecIsoL.isIrrSec h hIZ.2.2.1,
    SecIsoL.not_commOf_le h hIZ.2.2.2⟩

private theorem good_of_commOf_le {L A : Subgroup (MulAut W)} {M M' : Subgroup W}
    (hMinvL : XMod.IsInv ↥L M) (hM'invL : XMod.IsInv ↥L M')
    (hIrrL : XMod.IsIrrSec ↥L M' M) (hc : XMod.commOf ↥L M ≤ M') (hP : Good L A M') :
    Good L A M := by
  have hM'M : M' ≤ M := hIrrL.1.le
  have key : ∀ I Z : Subgroup W, I ≤ M → IsGomiNoncentralFactor L I Z →
      IsGomiNoncentralFactor L (I ⊓ M') (Z ⊓ M') ∧ SecIsoL L I Z (I ⊓ M') (Z ⊓ M') := by
    intro I Z hIM hIZ
    obtain ⟨hIinv, hZinv, hirr, hnc⟩ := hIZ
    have hsec : SecIsoL L I Z (I ⊓ M') (Z ⊓ M') := by
      rcases secIsoL_or_secIsoL_inf hMinvL hM'invL hIrrL hIM hIinv hZinv hirr with h | h
      · exact absurd hc (SecIsoL.not_commOf_le h hnc)
      · exact h
    exact ⟨isGomiNoncentralFactor_inf hM'invL ⟨hIinv, hZinv, hirr, hnc⟩ hsec, hsec⟩
  unfold Good at hP
  rcases hP with hno | ⟨I₀, Z₀, hZ₀I₀, hI₀M', hLI₀, hLZ₀, hAI₀, hAZ₀, hNCF₀, hrep⟩
  · refine Or.inl ?_
    rintro ⟨I, Z, hIM, hNCF⟩
    exact hno ⟨I ⊓ M', Z ⊓ M', inf_le_right, (key I Z hIM hNCF).1⟩
  · refine Or.inr ⟨I₀, Z₀, hZ₀I₀, hI₀M'.trans hM'M, hLI₀, hLZ₀, hAI₀, hAZ₀, hNCF₀, ?_⟩
    intro I Z hIM hNCF
    have h1 := (key I Z hIM hNCF).1
    exact (key I Z hIM hNCF).2.trans (hrep (I ⊓ M') (Z ⊓ M') inf_le_right h1)

private theorem secIsoL_top_of_homogeneity [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hH : GomiFact36Homogeneity) (hN : GomiFact36Identification) {L A : Subgroup (MulAut W)}
    {V₀ : Subgroup W} (hfaith : FaithfulOn L A V₀) (hChev : IsGomiChevTwo ↥L)
    (hLie : IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L))
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    (hAq : IsQuadratic A) (hAnc : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    (hcost : OffenderCost A) (hV₀fix : V₀ ≤ fixV (centIn A L)) {M M' I₀ Z₀ : Subgroup W}
    (hMV : M ≤ V₀) (hI₀M' : I₀ ≤ M') (hM'V : M' ≤ V₀) (hMinvL : XMod.IsInv ↥L M)
    (hM'invL : XMod.IsInv ↥L M') (hMinvA : XMod.IsInv ↥A M) (hM'invA : XMod.IsInv ↥A M')
    (hIrrL : XMod.IsIrrSec ↥L M' M) (hc : ¬ XMod.commOf ↥L M ≤ M')
    (hLI₀ : XMod.IsInv ↥L I₀) (hLZ₀ : XMod.IsInv ↥L Z₀) (hAI₀ : XMod.IsInv ↥A I₀)
    (hAZ₀ : XMod.IsInv ↥A Z₀) (hNCF₀ : IsGomiNoncentralFactor L I₀ Z₀) :
    SecIsoL L I₀ Z₀ M M' := by
  have hMM' : M' ≤ M := hIrrL.1.le
  have hI₀V : I₀ ≤ V₀ := hI₀M'.trans hM'V
  have hsI : L ≤ stabSub I₀ := le_stabSub_of_isInv hLI₀
  have hsZ : L ≤ stabSub Z₀ := le_stabSub_of_isInv hLZ₀
  have haI : A ≤ stabSub I₀ := le_stabSub_of_isInv hAI₀
  have haZ : A ≤ stabSub Z₀ := le_stabSub_of_isInv hAZ₀
  have hsM : L ≤ stabSub M := le_stabSub_of_isInv hMinvL
  have hsM' : L ≤ stabSub M' := le_stabSub_of_isInv hM'invL
  have haM : A ≤ stabSub M := le_stabSub_of_isInv hMinvA
  have haM' : A ≤ stabSub M' := le_stabSub_of_isInv hM'invA
  have hNCFM : IsGomiNoncentralFactor L M M' := ⟨hMinvL, hM'invL, hIrrL, hc⟩
  have hnc₀ : ¬ XMod.commOf ↥L I₀ ≤ Z₀ := hNCF₀.2.2.2
  have hZI₀ : Z₀ ≤ I₀ := hNCF₀.2.2.1.1.le
  have hf₀ := autSec_offender_facts hChev.1 hAL hAe hAq hAnc hcost hV₀fix hsI hsZ haI haZ hI₀V hnc₀
  have hfM := autSec_offender_facts hChev.1 hAL hAe hAq hAnc hcost hV₀fix hsM hsM' haM haM' hMV hc
  have hnat₀ := isGomiNatural_of_ncf hN hW hfaith hChev hLie hAL hAe hAq hAnc hcost hV₀fix hsI hsZ
    haI haZ hI₀V hNCF₀
  have hnatM := isGomiNatural_of_ncf hN hW hfaith hChev hLie hAL hAe hAq hAnc hcost hV₀fix hsM hsM'
    haM haM' hMV hNCFM
  have hk₀ := inf_centSec_eq hChev.1 hAL hV₀fix hsI hsZ hI₀V hnc₀
  have hkM := inf_centSec_eq hChev.1 hAL hV₀fix hsM hsM' hMV hc
  have hcard := card_autSec_eq hChev.1 hAL hV₀fix hsI hsZ haI haZ hI₀V hnc₀ hsM hsM' haM haM'
    hMV hc
  have hle := card_sec_mul_card_sec_le hZI₀ hI₀M' hMM' haI haZ haM haM' (hcost M)
    (by rw [hkM]; exact le_centSec_bot_of_le_fixV (hMV.trans hV₀fix))
  rw [← hcard] at hle
  exact hH W hW L A I₀ Z₀ M M' hChev hLie hAL haI haZ haM haM' hNCF₀ hNCFM hnat₀ hnatM hf₀.1
    (hk₀.trans hkM.symm) hf₀.2.1 hf₀.2.2.1 hfM.2.2.1 hle

private theorem good_of_not_commOf_le [Finite W] (hH : GomiFact36Homogeneity)
    (hN : GomiFact36Identification) (hW : ∀ w : W, w ^ 2 = 1) {L A : Subgroup (MulAut W)}
    {V₀ : Subgroup W} (hfaith : FaithfulOn L A V₀) (hChev : IsGomiChevTwo ↥L)
    (hLie : IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L))
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    (hAq : IsQuadratic A) (hAnc : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    (hcost : OffenderCost A) (hV₀fix : V₀ ≤ fixV (centIn A L)) {M M' : Subgroup W}
    (hMV : M ≤ V₀) (hM'V : M' ≤ V₀) (hMinvL : XMod.IsInv ↥L M) (hM'invL : XMod.IsInv ↥L M')
    (hMinvA : XMod.IsInv ↥A M) (hM'invA : XMod.IsInv ↥A M') (hIrrL : XMod.IsIrrSec ↥L M' M)
    (hc : ¬ XMod.commOf ↥L M ≤ M') (hP : Good L A M') : Good L A M := by
  have hM'M : M' ≤ M := hIrrL.1.le
  have hNCFM : IsGomiNoncentralFactor L M M' := ⟨hMinvL, hM'invL, hIrrL, hc⟩
  unfold Good at hP
  have key : ∀ I Z : Subgroup W, I ≤ M → IsGomiNoncentralFactor L I Z →
      SecIsoL L I Z M M' := by
    intro I Z hIM hIZ
    obtain ⟨hIinv, hZinv, hirr, hnc⟩ := hIZ
    rcases secIsoL_or_secIsoL_inf hMinvL hM'invL hIrrL hIM hIinv hZinv hirr with h | h
    · exact h
    · have hNCF' : IsGomiNoncentralFactor L (I ⊓ M') (Z ⊓ M') :=
        isGomiNoncentralFactor_inf hM'invL ⟨hIinv, hZinv, hirr, hnc⟩ h
      rcases hP with hno | ⟨I₀, Z₀, hZ₀I₀, hI₀M', hLI₀, hLZ₀, hAI₀, hAZ₀, hNCF₀, hrep⟩
      · exact absurd ⟨I ⊓ M', Z ⊓ M', inf_le_right, hNCF'⟩ hno
      · exact SecIsoL.trans (SecIsoL.trans h (hrep _ _ inf_le_right hNCF'))
          (secIsoL_top_of_homogeneity hW hH hN hfaith hChev hLie hAL hAe hAq hAnc hcost hV₀fix hMV
            hI₀M' hM'V hMinvL hM'invL hMinvA hM'invA hIrrL hc hLI₀ hLZ₀ hAI₀ hAZ₀ hNCF₀)
  exact Or.inr ⟨M, M', hM'M, le_rfl, hMinvL, hM'invL, hMinvA, hM'invA, hNCFM, key⟩

private theorem good_of_le [Finite W] (hN : GomiFact36Identification)
    (hH : GomiFact36Homogeneity) (hW : ∀ w : W, w ^ 2 = 1) {L A : Subgroup (MulAut W)}
    (hChev : IsGomiChevTwo ↥L)
    (hLie : IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L))
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A)
    (hAq : IsQuadratic A) (hAnc : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    (hcost : OffenderCost A) {V₀ : Subgroup W} (hfaith : FaithfulOn L A V₀)
    (hV₀fix : V₀ ≤ fixV (centIn A L)) :
    ∀ M : Subgroup W, M ≤ V₀ → XMod.IsInv ↥L M → XMod.IsInv ↥A M → Good L A M := by
  have hfin : Finite (Subgroup W) :=
    Finite.of_injective (fun H : Subgroup W => (H : Set W)) SetLike.coe_injective
  intro M
  induction M using WellFoundedLT.induction with
  | _ M ih =>
    intro hMV hMinvL hMinvA
    by_cases hbot : M = ⊥
    · rw [hbot]
      exact good_bot
    · obtain ⟨M', hM'ltM, hM'invL, hM'invA, hmax⟩ :=
        exists_max_invariant_lt hbot
      have hM'V : M' ≤ V₀ := hM'ltM.le.trans hMV
      have hIrrMA : XMod.IsIrrSec ↥(L ⊔ A) M' M := isIrrSec_sup_of_max hM'ltM hmax
      have hIrrL : XMod.IsIrrSec ↥L M' M :=
        isIrrSec_of_isIrrSec_sup_max hW hChev hAL hAe hAq hcost hV₀fix hMV hMinvL hM'invL
          hMinvA hM'invA hIrrMA
      have hP : Good L A M' := ih M' hM'ltM hM'V hM'invL hM'invA
      by_cases hc : XMod.commOf ↥L M ≤ M'
      · exact good_of_commOf_le hMinvL hM'invL hIrrL hc hP
      · exact good_of_not_commOf_le hH hN hW hfaith hChev hLie hAL hAe hAq hAnc hcost hV₀fix hMV
          hM'V hMinvL hM'invL hMinvA hM'invA hIrrL hc hP

theorem GomiFact36Hyp.chiefFactors_of_inputs (hN : GomiFact36Identification)
    (hH : GomiFact36Homogeneity) (hF : GomiFact36Faithful) [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (h : GomiFact36Hyp Y S L) :
    (∀ I Z : Subgroup W, I ≤ G6.submoduleClosure L (fixV S) → IsGomiNoncentralFactor L I Z →
        IsGomiNatural L I Z) ∧
      ∀ I Z I' Z' : Subgroup W, I ≤ G6.submoduleClosure L (fixV S) →
        I' ≤ G6.submoduleClosure L (fixV S) → IsGomiNoncentralFactor L I Z →
        IsGomiNoncentralFactor L I' Z' → SecIsoL L I Z I' Z' := by
  have hChev : IsGomiChevTwo ↥L := h.2.2.2.2.2.1
  have hLie : IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L) :=
    h.2.2.2.2.2.2
  obtain ⟨A, hAS, hAL, hAe, hAq, hAnc, hcost⟩ := GomiFact36Hyp.exists_offender hW h
  let V₀ : Subgroup W := G6.submoduleClosure L (fixV S)
  have hV₀stab : L ⊔ (S ⊓ Subgroup.normalizer (L : Set (MulAut W))) ≤ stabSub V₀ :=
    sup_le_stabSub_submoduleClosure_fixV S L
  have hV₀invL : XMod.IsInv ↥L V₀ := isInv_of_le_stabSub (le_sup_left.trans hV₀stab)
  have hV₀invA : XMod.IsInv ↥A V₀ :=
    isInv_of_le_stabSub ((le_inf hAS hAL).trans le_sup_right |>.trans hV₀stab)
  have hV₀fix : V₀ ≤ fixV (centIn A L) :=
    submoduleClosure_fixV_le_fixV (inf_le_left.trans hAS) inf_le_right
  have hfaith : FaithfulOn L A V₀ := hF W hW Y S L A h hAS hAL hAe hAq hAnc hcost
  have hG : Good L A V₀ :=
    good_of_le hN hH hW hChev hLie hAL hAe hAq hAnc hcost hfaith hV₀fix V₀ le_rfl hV₀invL hV₀invA
  unfold Good at hG
  rcases hG with hno | ⟨I₀, Z₀, hZ₀I₀, hI₀V, hLI₀, hLZ₀, hAI₀, hAZ₀, hNCF₀, hrep⟩
  · exact ⟨fun I Z hIV hIZ => absurd ⟨I, Z, hIV, hIZ⟩ hno,
      fun I Z I' Z' hIV _ hIZ _ => absurd ⟨I, Z, hIV, hIZ⟩ hno⟩
  · have hnat : IsGomiNatural L I₀ Z₀ :=
      isGomiNatural_of_ncf hN hW hfaith hChev hLie hAL hAe hAq hAnc hcost hV₀fix
        (le_stabSub_of_isInv hLI₀) (le_stabSub_of_isInv hLZ₀) (le_stabSub_of_isInv hAI₀)
        (le_stabSub_of_isInv hAZ₀) hI₀V hNCF₀
    exact ⟨fun I Z hIV hIZ => isGomiNatural_of_secIsoL hnat (hrep I Z hIV hIZ),
      fun I Z I' Z' hIV hI'V hIZ hIZ' =>
        SecIsoL.trans (hrep I Z hIV hIZ) (SecIsoL.symm (hrep I' Z' hI'V hIZ'))⟩

theorem gomiFact36ChiefFactors_of_inputs (hN : GomiFact36Identification)
    (hH : GomiFact36Homogeneity) (hF : GomiFact36Faithful) : GomiFact36ChiefFactors :=
  fun _ _ _ hW _ _ _ h => h.chiefFactors_of_inputs hN hH hF hW

end CFSG.GroupTheory

end
