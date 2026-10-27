module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzSylowFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzGlueEdge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzGlueFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SSuzSteps

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem commutator_oddIn_le_wGroup_of_suz
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    {t : G} {P : Subgroup G}
    (h : L34NormalSettingAt (fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz) G t P)
    (hsuz : Blueprint.NativeSporadic.IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .Suz) (htP : t ∉ P)
    {W : Subgroup G} (hPW : P ≤ normalizer (W : Set G))
    (hWE : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → wGroup E = W) :
    ⁅oddIn P, P⁆ ≤ W := by
  have hsimple := h.1.1
  have hna := h.1.2.1
  have hK := h.1.2.2.1
  have ht := h.2.1
  have hPt := h.2.2.1
  have hPc := h.2.2.2.1
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨E, H, hEP, hE, hHP, -, hHfix, hnc⟩ :=
    exists_kleinFour_perfect_of_suz h.commutator_self hsuz
  have hE2 : IsElemTwo E :=
    ⟨fun a ha b hb => congrArg Subtype.val (mul_comm_of_exponent_two hE.exponent_two
      (⟨a, ha⟩ : E) ⟨b, hb⟩), fun a ha => congrArg Subtype.val (IsKleinFour.mul_self (⟨a, ha⟩ : E))⟩
  have htE : ∀ y ∈ E, t * y = y * t := fun y hy =>
    (mem_centralizer_singleton_iff.mp (hPt (hEP hy))).symm
  obtain ⟨hEt2, hEt8⟩ := GrS5.elemTwo_zpowers_sup htt hE2 htE fun htE' => htP (hEP htE')
  have hEtC : zpowers t ⊔ E ≤ centralizer ({t} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) (hEP.trans hPt)
  have hWEt : wGroup (zpowers t ⊔ E) = W := by
    refine hWE _ hEtC ⟨isMulCommutative_iff_of_setLike.mpr hEt2.1, fun x hx => ?_⟩ ?_
    · rw [pow_two]
      exact hEt2.2 x hx
    · rw [hEt8, hE.card_four]
  refine commutator_oddIn_le_of_kleinFour hE hEP hHP hPW (fun f hfE hf1 => ?_) hnc
  have hfP : f ∈ P := hEP hfE
  have hf2 : orderOf f = 2 := orderOf_eq_prime (by rw [pow_two]; exact hE2.2 f hfE) hf1
  have hft : f ≠ t := fun hft => htP (hft ▸ hfP)
  have hftC : f * t = t * f := mem_centralizer_singleton_iff.mp (hPt hfP)
  have hft2 : orderOf (f * t) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hft ?_
    · rw [pow_two, mul_assoc, ← mul_assoc t, ← hftC, mul_assoc, htt, mul_one,
        hE2.2 f hfE]
    · calc f = f * t * t := by rw [mul_assoc, htt, mul_one]
        _ = t := by rw [h1, one_mul]
  have hC : ∀ {z : G}, orderOf z = 2 → centralizer ({z} : Set G) ≠ ⊤ := fun {z} hz htop =>
    GSLit.not_mem_center_of_orderOf_eq_two hna hz (mem_center_iff.mpr fun g =>
      (mem_centralizer_singleton_iff.mp (htop ▸ mem_top g : g ∈ centralizer ({z} : Set G))))
  have hC1 := commutator_fixedLayer_le_wGroup hS hU hheld hK ht hPt hPc hfP hf2 hft (hC hf2)
    (hC hft2)
  calc ⁅oddIn P ⊓ centralizer ({f} : Set G), H⁆
      ≤ ⁅oddIn P ⊓ centralizer ({f} : Set G), gsFixedLayer P f⁆ :=
        commutator_mono le_rfl (hHfix f hfE hf1)
    _ ≤ wGroup (zpowers f ⊔ zpowers t) := hC1.trans inf_le_right
    _ ≤ wGroup (zpowers t ⊔ E) := wGroup_mono (by
        rw [sup_comm]
        exact sup_le_sup_left (zpowers_le.mpr hfE) _)
    _ = W := hWEt

theorem l34SuzSignalizerGluing_of_facts
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hF1 : SuzSylowFacts) (hF2 : TwoSuzSylowFacts) : L34SuzSignalizerGluing := by
  intro G _ _ t P h
  obtain ⟨W, hWo, hNW, hWE, -⟩ := exists_wGroup_glue_of_sylowData h.gwTwoBalanced h.2.1 h.2.2.1
    h.centralizer_le_normalizer (GrS4.le_normalizer_oddIn_self P) (odd_card_oddIn P)
    (suzSylowData_of_facts hF1 hF2 h)
  refine ⟨W, hWo, hNW, hWE, fun hZ => ?_⟩
  rcases h.suz_cover with ⟨-, hsuz, htP⟩ | ⟨h2, -, -⟩
  · exact commutator_oddIn_le_wGroup_of_suz hS hU hheld h hsuz htP (le_normalizer.trans hNW) hWE
  · rw [hZ, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
