module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullCanonicalKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOriginalSylowProduct

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.BenderSuzuki.PFAppendixIII

universe v

variable {G : Type v} [Group G]

@[expose] def rankTwoCentralizerSylowData (H : Subgroup G) (z u : G) : Prop :=
  let M := Subgroup.centralizer ({u} : Set G)
  let L := localInvolutionPointHull z u
  let U := originalPointRoot H z u
  ∀ T1 : Sylow 2 ↥(H ⊓ M),
    let A := (T1 : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype
    let T := A ⊓ (L ⊔ (M ⊓ Subgroup.centralizer (L : Set G)))
    (∃ S : Sylow 2 M, (S : Subgroup M).map M.subtype = A) ∧
    {x : G | x ∈ A ∧ orderOf x = 2} =
      ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
        ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
    (CFSG.omega₁ (G := A) (p := 2)).map A.subtype = Subgroup.zpowers u ⊔ U ∧
    CFSG.omega₁ (G := A) (p := 2) = (Subgroup.zpowers u ⊔ U).subgroupOf A ∧
    Disjoint (Subgroup.zpowers u) U ∧
    (∀ e ∈ Subgroup.zpowers u, ∀ k ∈ U, Commute e k) ∧
    IsElementaryAbelian 2 ↥(Subgroup.zpowers u ⊔ U : Subgroup G) ∧
    (∃ e : Subgroup.zpowers u × U ≃*
      ↥((CFSG.omega₁ (G := A) (p := 2)).map A.subtype),
      ∀ (a : Subgroup.zpowers u) (b : U), (e (a, b) : G) = (a : G) * b) ∧
    {x : G | x ∈ T ∧ orderOf x = 2} = {x : G | x ∈ A ∧ orderOf x = 2} ∧
    {x : G | x ∈ T ∧ orderOf x = 2} =
      ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
        ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
    (CFSG.omega₁ (G := T) (p := 2)).map T.subtype =
      (CFSG.omega₁ (G := A) (p := 2)).map A.subtype ∧
    (CFSG.omega₁ (G := T) (p := 2)).map T.subtype = Subgroup.zpowers u ⊔ U ∧
    CFSG.omega₁ (G := T) (p := 2) = (Subgroup.zpowers u ⊔ U).subgroupOf T ∧
    (∃ e : Subgroup.zpowers u × U ≃*
      ↥((CFSG.omega₁ (G := T) (p := 2)).map T.subtype),
      ∀ (a : Subgroup.zpowers u) (b : U), (e (a, b) : G) = (a : G) * b)

variable [Finite G]

theorem original_rank_two_centralizer_sylow_data
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type v) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (huz : Commute u z)
    (hescape : ¬ Subgroup.centralizer ({u} : Set G) ≤ H)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z u)) :
    rankTwoCentralizerSylowData H z u := by
  have hcentral := original_local_hull_entire_oddCore_central
    h hcomm hsmallerR1 u hu huz hescape hrank
  have hpoint := every_original_point_sylow_entire_involutions_and_product
    h beta hbeta hpairRank.le u huD hu huz hescape hrank hcentral
  have hinter := every_original_point_sylow_literal_intersection_entire_product
    h beta hbeta hpairRank.le u huD hu huz hescape hrank hcentral
  unfold rankTwoCentralizerSylowData
  simp only [order_two_iff_isInvolution]
  intro T1
  obtain ⟨hS, hInv, hOmMap, hOm, hdisj, hcommute, helem, he⟩ := hpoint T1
  obtain ⟨_hS, hInvSame, hInvT, hOmSame, hOmMapT, hOmT,
    _hdisj, _hcommute, _helem, heT⟩ := hinter T1
  exact ⟨hS, hInv, hOmMap, hOm, hdisj, hcommute, helem, he,
    hInvSame, hInvT, hOmSame, hOmMapT, hOmT, heT⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
