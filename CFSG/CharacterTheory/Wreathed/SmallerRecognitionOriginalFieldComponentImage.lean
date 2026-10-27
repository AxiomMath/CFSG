module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldReducedImage
public import CFSG.CharacterTheory.Wreathed.ComponentCoveringLocalQuotient

public noncomputable section
namespace CFSG.Wreathed.SmallerRecognitionOriginalField
open ComponentCoveringLocal FullSylowCoveringObstruction ReducedCentralizerInclusion
open SimpleOddIndexQuotient
open scoped Classical
variable {G : Type} [Group G] [Finite G]

@[expose] def componentCentralizerReducedIntersectionEquiv (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) :
    Subgroup.centralizer {coveringInvolution n S e K hSK} ⧸
      CFSG.oddCore (Subgroup.centralizer {coveringInvolution n S e K hSK}) ≃*
      originalCentralizerSubgroup n S e K ⧸
        CFSG.oddCore (originalCentralizerSubgroup n S e K) :=
  QuotientGroup.congr _ _ (coveringCentralizerIntersectionEquiv n S e K hSK)
    (CFSG.ComponentClassification.OddCore.equiv_invariant
      (coveringCentralizerIntersectionEquiv n S e K hSK))

omit [Finite G] in
theorem componentCentralizerReducedIntersectionEquiv_mk (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (c : Subgroup.centralizer {coveringInvolution n S e K hSK}) :
    componentCentralizerReducedIntersectionEquiv n S e K hSK
      (QuotientGroup.mk' (CFSG.oddCore _) c) =
      QuotientGroup.mk' (CFSG.oddCore (originalCentralizerSubgroup n S e K))
        (coveringCentralizerIntersectionEquiv n S e K hSK c) := by
  exact QuotientGroup.congr_mk' _ _ _ _ c

@[expose] def componentCentralizerReducedImageEquiv (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal) :
    Subgroup.centralizer {coveringInvolution n S e K hSK} ⧸
      CFSG.oddCore (Subgroup.centralizer {coveringInvolution n S e K hSK}) ≃*
        originalImage n S e K :=
  (componentCentralizerReducedIntersectionEquiv n S e K hSK).trans
    (Classical.choose (original_centralizer_odd_core_quotient_equiv n S e K hnormal))

theorem componentCentralizerReducedImageEquiv_mk (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (c : Subgroup.centralizer {coveringInvolution n S e K hSK}) :
    componentCentralizerReducedImageEquiv n S e K hSK hnormal
      (QuotientGroup.mk' (CFSG.oddCore _) c) =
      originalImageMap n S e K (coveringCentralizerIntersectionEquiv n S e K hSK c) := by
  change Classical.choose (original_centralizer_odd_core_quotient_equiv n S e K hnormal)
    (componentCentralizerReducedIntersectionEquiv n S e K hSK
      (QuotientGroup.mk' (CFSG.oddCore _) c)) = _
  rw [componentCentralizerReducedIntersectionEquiv_mk]
  exact (Classical.choose_spec
    (original_centralizer_odd_core_quotient_equiv n S e K hnormal)).1 _

theorem componentCentralizerReducedImageEquiv_symm (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (c : Subgroup.centralizer {coveringInvolution n S e K hSK}) :
    (componentCentralizerReducedImageEquiv n S e K hSK hnormal).symm
      (originalImageMap n S e K (coveringCentralizerIntersectionEquiv n S e K hSK c)) =
      QuotientGroup.mk' (CFSG.oddCore _) c := by
  rw [← componentCentralizerReducedImageEquiv_mk n S e K hSK hnormal c]
  exact MulEquiv.symm_apply_apply _ _

@[expose] def componentSimpleReducedCentralizerImage
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    coveringSimpleReducedCentralizer n hn S e K hSK L hodd →* originalImage n S e K :=
  reducedCentralizerImageInclusion (CFSG.oddCore K) (actual_oddCore_odd K) L hodd
    (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK)
    (originalImage n S e K) (componentCentralizerReducedImageEquiv n S e K hSK hnormal)

theorem componentSimpleReducedCentralizerImage_data
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    Function.Injective (componentSimpleReducedCentralizerImage n hn S e K hSK hnormal L hodd) ∧
      (componentSimpleReducedCentralizerImage n hn S e K hSK hnormal L hodd).range.Normal ∧
      Odd (componentSimpleReducedCentralizerImage n hn S e K hSK hnormal L hodd).range.index :=
  let h := reducedCentralizerImageInclusion_data (CFSG.oddCore K) (actual_oddCore_odd K) L hodd
    (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK)
    (originalImage n S e K) (componentCentralizerReducedImageEquiv n S e K hSK hnormal)
  ⟨h.1, h.2.1, h.2.2.1⟩

@[expose] def componentSimpleReducedCentralizerInclusion
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    coveringSimpleReducedCentralizer n hn S e K hSK L hodd →*
      centralizerOddCoreQuotient n S e :=
  (originalImage n S e K).subtype.comp
    (componentSimpleReducedCentralizerImage n hn S e K hSK hnormal L hodd)

theorem componentSimpleReducedCentralizerInclusion_mk
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hnormal : (originalImage n S e K).Normal)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index)
    (c : Subgroup.centralizer {coveringInvolution n S e K hSK})
    (b : Subgroup.centralizer ({coveringQuotientInvolution n hn S e K hSK L hodd} : Set L))
    (hcb : QuotientGroup.mk' (CFSG.oddCore K) (c : K) = ((b : L) : K ⧸ CFSG.oddCore K)) :
    componentSimpleReducedCentralizerInclusion n hn S e K hSK hnormal L hodd
      (QuotientGroup.mk' (CFSG.oddCore _) b) =
      centralizerOddCoreMap n S e (coveringCentralizerInclusion n S e K hSK c) := by
  have h := (reducedCentralizerImageInclusion_data (CFSG.oddCore K) (actual_oddCore_odd K)
    L hodd (coveringInvolution n S e K hSK) (coveringInvolution_order n hn S e K hSK)
    (originalImage n S e K) (componentCentralizerReducedImageEquiv n S e K hSK hnormal)).2.2.2
    c b hcb
  change (componentSimpleReducedCentralizerImage n hn S e K hSK hnormal L hodd
    (QuotientGroup.mk' (CFSG.oddCore _) b) : centralizerOddCoreQuotient n S e) = _
  rw [show componentSimpleReducedCentralizerImage n hn S e K hSK hnormal L hodd
      (QuotientGroup.mk' (CFSG.oddCore _) b) =
      componentCentralizerReducedImageEquiv n S e K hSK hnormal
        (QuotientGroup.mk' (CFSG.oddCore _) c) from h,
    componentCentralizerReducedImageEquiv_mk, originalImageMap_coe]
  rfl

end CFSG.Wreathed.SmallerRecognitionOriginalField
