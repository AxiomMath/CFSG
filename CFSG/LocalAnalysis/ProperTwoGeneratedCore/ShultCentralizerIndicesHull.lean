module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairCentralizerModel

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionConjugateHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
open CFSG.BenderSuzuki.PFAppendixIII

universe u v w

variable {G : Type u} [Group G] [Finite G]

theorem product_hull_model_of_full_model_pair
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {u : G} (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (hut : Commute u t) (huz : Commute u z)
    (hodd : CFSG.oddCore (localInvolutionPointHull z u) = ⊥)
    {F : Type v} [Group F] [Finite F] {Ξ : Type w} (rho : F →* Equiv.Perm Ξ) (b : Ξ)
    (B : Subgroup F) (q : ℕ) (hmodel : FullModelPointPair rho b B q)
    (e : localInvolutionPointHull z u ≃* F) :
    let L₁ := localInvolutionPointHull z (u * t)
    (L₁.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal ∧ t ∈ L₁ ∧
      (∀ s ∈ L₁, orderOf s = 2 → s ∈ involutionPointClass z) ∧ CFSG.oddCore L₁ = ⊥ ∧
      Nonempty (L₁ ≃* F) ∧ Nat.card (elementFixedSet H (u * t)) = Nat.card Ξ := by
  intro L₁
  classical
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have htclass : t ∈ involutionPointClass z := ht.1
  have hflip : pointRightCosetMul H (rightCosetMk H 1) t = beta := by
    rw [pointRightCosetMul_eq_translate]
    exact ht.2
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huD
  have hescape := original_pair_centralizer_escapes H beta hbeta u t hut hflip
  obtain ⟨-, htL, -, -, hP⟩ :=
    original_pair_local_hull_inputs h.local_datum beta hbeta u t hu huz hut htclass hflip
  obtain ⟨hclassL, -, hinvL⟩ := original_local_hull_internal_class h.local_datum u huz hP
  have hI : ∀ y ∈ localInvolutionPointHull z u, orderOf y = 2 →
      y ∈ involutionPointClass z :=
    fun y hy hyo => ((Set.ext_iff.mp hinvL y).mp ⟨hy, hyo⟩).1
  have hzt : ∃ l ∈ localInvolutionPointHull z u, rightConjugateElem z l = t := by
    have htI : (⟨t, htL⟩ : localInvolutionPointHull z u) ∈
        involutionPointClass (⟨z, distinguished_mem_localInvolutionPointHull huz⟩ :
          localInvolutionPointHull z u) := by
      rw [hclassL]
      exact (Subgroup.orderOf_coe (⟨t, htL⟩ : localInvolutionPointHull z u)).symm.trans
        (order_two_of_mem_pointClass h.local_datum.distinguished_order htclass)
    obtain ⟨l, hl⟩ := htI
    exact ⟨l, l.property, congrArg Subtype.val hl⟩
  have hfull := original_central_sylow_local_hull_full_fixed_set h.local_datum S hzS hzcenter
    u huH hu huz hescape
  have hrk := rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm
    hsmallerR1 beta hbeta hpairRank huD hu huz hescape (Classical.arbitrary _)
    (Classical.arbitrary _)
  dsimp only at hrk
  obtain ⟨-, -, -, -, -, _U, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    huzclass, -⟩ := hrk
  let : MulAction F Ξ := MulAction.compHom Ξ rho
  obtain ⟨hBb, hrank, hSE, hdouble, -⟩ := hmodel
  obtain ⟨-, g, -, -, hnormal, htL₁, hI₁, hodd₁, -, E, f, -⟩ :=
    original_pair_product_hull_conjugation h.local_datum beta hbeta u t hu huz hut htclass
      hflip hfull hI hodd hzt huzclass e hrank hdouble b (hBb ▸ hSE)
  exact ⟨hnormal, htL₁, hI₁, hodd₁, ⟨E⟩, Nat.card_congr f⟩

end CFSG.ProperTwoGeneratedCore.RankOnePair
