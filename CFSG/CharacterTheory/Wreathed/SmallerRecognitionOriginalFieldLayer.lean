module

public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldLayerTransport
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldCore

public noncomputable section

namespace CFSG.Wreathed.SmallerRecognitionOriginalField

open ActualProjectiveLayer ActualCentralizerSemilinear NormalOddIndexFullCenterLayer

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
@[expose] def originalFullCenterQuotientEquiv (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerOddCoreQuotient n S e ⧸ Subgroup.center (centralizerOddCoreQuotient n S e) ≃*
      centralizerFullQuotient n hn S e :=
  QuotientGroup.quotientMulEquivOfEq
    (centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e)

omit [IsSimpleGroup G] in
theorem originalFullCenterQuotientEquiv_mk (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (h : centralizerOddCoreQuotient n S e) :
    originalFullCenterQuotientEquiv n hn S e
      (QuotientGroup.mk' (Subgroup.center (centralizerOddCoreQuotient n S e)) h) =
      centralizerFullQuotientMap n hn S e h := rfl

theorem original_centralizer_layer_inputs
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    let H := centralizerOddCoreQuotient n S e
    let M := CFSG.layer H
    M.Normal ∧ CFSG.IsQuasisimple M ∧ Even (Nat.card (M ⧸ Subgroup.center M)) ∧
      IsPGroup 2 (Subgroup.center H) ∧
      Subgroup.centralizer (M : Set H) = Subgroup.center H := by
  let H := centralizerOddCoreQuotient n S e
  let M := CFSG.layer H
  let ML := centralizerLiftedLayer n hn S e
  have hU := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  have hcomp := actual_layer_component_data hnonab n hn S e hfour
  let E := centralizerActualLayerEquiv hnonab n hn S e hfour
  let E₀ : M ⧸ Subgroup.center M ≃* ML ⧸ Subgroup.center ML :=
    QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)
  have hker : Subgroup.center ML = (centralizerLiftedLayerMap n hn S e).ker :=
    hU.center.trans hU.restriction_kernel.symm
  let E₁ : ML ⧸ Subgroup.center ML ≃* centralizerSimpleLayer n hn S e :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans hU.actual_quotient.some
  have heven : Even (Nat.card (M ⧸ Subgroup.center M)) := by
    rw [Nat.card_congr (E₀.trans E₁).toEquiv]
    exact centralizerSimpleLayer_even hnonab n hn S e hfour
  have htwo : IsPGroup 2 (Subgroup.center H) := by
    rw [centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e]
    exact IsPGroup.of_card (centralizerFullCenterImage_card n hn S e)
  exact ⟨actual_layer_normal hnonab n hn S e hfour, hcomp.1.1, heven, htwo,
    hcomp.2.2.2.1.trans (centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e).symm⟩


theorem original_full_center_layer_simple
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    let H := centralizerOddCoreQuotient n S e
    let P := CFSG.generalizedFitting (H ⧸ Subgroup.center H)
    IsSimpleGroup P ∧ (∃ a b : P, a * b ≠ b * a) ∧
      Subgroup.centralizer (P : Set (H ⧸ Subgroup.center H)) = ⊥ := by
  let H := centralizerOddCoreQuotient n S e
  let M := CFSG.layer H
  obtain ⟨hMN, hM, _, _, hc⟩ := original_centralizer_layer_inputs hnonab n hn S e hfour
  let : M.Normal := hMN
  have hP := ambient_generalizedFitting M hM hc
  have hs := projectiveImage_simple M hM hc
  refine ⟨hP.symm ▸ hs.1, hP.symm ▸ hs.2, ?_⟩
  exact ambient_layer_centralizer M hM hc

@[expose] def originalFullCenterLayerEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* centralizerSimpleLayer n hn S e := by
  obtain ⟨hs, hab, hc⟩ := original_full_center_layer_simple hnonab n hn S e hfour
  let : IsSimpleGroup (CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
    Subgroup.center (centralizerOddCoreQuotient n S e))) := hs
  exact DegreeThreeModelFullCenter.generalizedFittingSimpleEquiv
    (originalFullCenterQuotientEquiv n hn S e) hab hc

theorem originalFullCenterLayerEquiv_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (a : CFSG.generalizedFitting (centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e))) :
    (originalFullCenterLayerEquiv hnonab n hn S e hfour a : centralizerFullQuotient n hn S e) =
      originalFullCenterQuotientEquiv n hn S e (a : _) := rfl


omit [IsSimpleGroup G] in
@[expose] def coveringQuotientInvolution
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) : L :=
  ⟨QuotientGroup.mk' (CFSG.oddCore K) (FullSylowCoveringObstruction.coveringInvolution
    n S e K hSK), ReducedCentralizerInclusion.quotient_involution_mem (CFSG.oddCore K)
      (SimpleOddIndexQuotient.actual_oddCore_odd K) L hodd _
        (coveringInvolution_order n hn S e K hSK)⟩

omit [IsSimpleGroup G] in
theorem coveringQuotientInvolution_coe
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    (coveringQuotientInvolution n hn S e K hSK L hodd : K ⧸ CFSG.oddCore K) =
      QuotientGroup.mk' (CFSG.oddCore K)
        (FullSylowCoveringObstruction.coveringInvolution n S e K hSK) := rfl

omit [IsSimpleGroup G] in
theorem coveringQuotientInvolution_order
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    orderOf (coveringQuotientInvolution n hn S e K hSK L hodd) = 2 := by
  rw [← Subgroup.orderOf_coe, coveringQuotientInvolution_coe]
  exact OddNormalQuotientInvolutions.quotient_involution (CFSG.oddCore K)
    (SimpleOddIndexQuotient.actual_oddCore_odd K)
    (FullSylowCoveringObstruction.coveringInvolution n S e K hSK)
    (coveringInvolution_order n hn S e K hSK)

omit [IsSimpleGroup G] in
abbrev coveringSimpleReducedCentralizer
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :=
  let B := Subgroup.centralizer ({coveringQuotientInvolution n hn S e K hSK L hodd} : Set L)
  B ⧸ CFSG.oddCore B

theorem covering_simple_full_center_layer_identification
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hcover : centralizerOddCore n S e ⊔ K.subgroupOf (involutionCentralizer n S e) = ⊤)
    (L : Subgroup (K ⧸ CFSG.oddCore K)) [L.Normal] (hodd : Odd L.index) :
    let H_L := coveringSimpleReducedCentralizer n hn S e K hSK L hodd
    let i := simpleReducedCentralizerInclusion n hn S e K hSK hcover L hodd
    (Subgroup.center H_L).map i = Subgroup.center (centralizerOddCoreQuotient n S e) ∧
      ∃ E : CFSG.generalizedFitting (H_L ⧸ Subgroup.center H_L) ≃*
        centralizerSimpleLayer n hn S e,
        ∀ a : CFSG.generalizedFitting (H_L ⧸ Subgroup.center H_L),
          ∀ hcenter : (Subgroup.center H_L).map i =
            Subgroup.center (centralizerOddCoreQuotient n S e),
          (E a : centralizerFullQuotient n hn S e) =
            originalFullCenterQuotientEquiv n hn S e
              (injectiveFullCenterMap i hcenter (a : H_L ⧸ Subgroup.center H_L)) := by
  let H_L := coveringSimpleReducedCentralizer n hn S e K hSK L hodd
  let i : H_L →* centralizerOddCoreQuotient n S e :=
    simpleReducedCentralizerInclusion n hn S e K hSK hcover L hodd
  obtain ⟨hMN, hM, heven, htwo, hc⟩ :=
    original_centralizer_layer_inputs hnonab n hn S e hfour
  let : (CFSG.layer (centralizerOddCoreQuotient n S e)).Normal := hMN
  have hi : Function.Injective i :=
    simpleReducedCentralizerInclusion_injective n hn S e K hSK hcover L hodd
  have hnormal : i.range.Normal :=
    simpleReducedCentralizerInclusion_normal n hn S e K hSK hcover L hodd
  have hodd' : Odd i.range.index :=
    simpleReducedCentralizerInclusion_odd_index n hn S e K hSK hcover L hodd
  have h := injective_normal_odd_index_full_center_layer
    i hi hnormal hodd' (CFSG.layer (centralizerOddCoreQuotient n S e)) hM heven htwo hc
  obtain ⟨hcenter, hrest⟩ := h
  obtain ⟨hcenter', _, _, _, _, _, ⟨E, hE⟩, _, _, _⟩ := hrest
  let E₀ := originalFullCenterLayerEquiv hnonab n hn S e hfour
  refine ⟨hcenter, E.trans E₀, ?_⟩
  intro a hcenter''
  change (E₀ (E a) : centralizerFullQuotient n hn S e) = _
  rw [originalFullCenterLayerEquiv_coe, hE]
  rfl

end CFSG.Wreathed.SmallerRecognitionOriginalField
