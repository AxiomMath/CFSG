module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldComponentImage

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open ComponentCoveringLocal NormalOddIndexFullCenterLayer
open scoped Classical
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]


omit [IsSimpleGroup G] in
@[expose] def OriginalComponentFullCenterIdentification
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) : Prop :=
  let H_L := coveringSimpleReducedCentralizer n hn S e K hSK L hodd
  let i := componentSimpleReducedCentralizerInclusion n hn S e K hSK hnormal L hodd
  (Subgroup.center H_L).map i = Subgroup.center (centralizerOddCoreQuotient n S e) ∧
    ∃ E : CFSG.generalizedFitting (H_L ⧸ Subgroup.center H_L) ≃*
      centralizerSimpleLayer n hn S e,
      ∀ a : CFSG.generalizedFitting (H_L ⧸ Subgroup.center H_L),
        ∀ hcenter : (Subgroup.center H_L).map i =
          Subgroup.center (centralizerOddCoreQuotient n S e),
        (E a : centralizerFullQuotient n hn S e) =
          originalFullCenterQuotientEquiv n hn S e
            (injectiveFullCenterMap i hcenter (a : H_L ⧸ Subgroup.center H_L))
theorem component_simple_full_center_layer_identification
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : CFSG.layer (centralizerOddCoreQuotient n S e) ≤ originalImage n S e K)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    ∃ hnormal : (originalImage n S e K).Normal,
      OriginalComponentFullCenterIdentification n hn S e K hSK hnormal L hodd := by
  let H := centralizerOddCoreQuotient n S e
  let M := CFSG.layer H
  let D := originalImage n S e K
  obtain ⟨hDN, hDodd⟩ :=
    component_cover_image_normal_odd_index hnonab n hn S e hfour p f hp hpodd hf hmodel
      K hSK hcover
  let : D.Normal := hDN
  obtain ⟨hMN, hM, heven, htwo, hc⟩ :=
    original_centralizer_layer_inputs hnonab n hn S e hfour
  let : M.Normal := hMN
  let E0 := componentCentralizerReducedImageEquiv n S e K hSK hDN
  have h := reduced_centralizer_image_full_center (CFSG.oddCore K)
    (SimpleOddIndexQuotient.actual_oddCore_odd K) L hodd
    (FullSylowCoveringObstruction.coveringInvolution n S e K hSK)
    (coveringInvolution_order n hn S e K hSK) M D hM heven htwo hc hDodd E0
  obtain ⟨hcenter, hcenter', _, _, _, ⟨E1, hE1⟩, _, _, _⟩ := h
  let E2 := originalFullCenterLayerEquiv hnonab n hn S e hfour
  refine ⟨hDN, hcenter, E1.trans E2, ?_⟩
  intro a hcenter''
  change (E2 (E1 a) : centralizerFullQuotient n hn S e) = _
  rw [originalFullCenterLayerEquiv_coe]
  exact congrArg (originalFullCenterQuotientEquiv n hn S e) (hE1 a)

end CFSG.Wreathed.SmallerRecognitionOriginalField
