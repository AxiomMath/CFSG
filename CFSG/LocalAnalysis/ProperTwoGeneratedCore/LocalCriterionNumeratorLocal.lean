module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorAssembly
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoLocalHull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u v w

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem original_pair_centralizer_escapes
    (H : Subgroup G) (b : pointRightCosetSpace H) (hb : b ≠ rightCosetMk H 1)
    (u t : G) (hut : Commute u t)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b) :
    ¬ Subgroup.centralizer ({u} : Set G) ≤ H := by
  intro hCH
  have htH : t ∈ H := hCH (Subgroup.mem_centralizer_singleton_iff.mpr hut.symm)
  exact hb (hflip.symm.trans ((point_right_base_fixed_iff H t).mpr htH))

omit [Finite G] in
theorem original_pair_local_hull_inputs
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hb : b ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2) (huz : Commute u z) (hut : Commute u t)
    (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b) :
    let L := localInvolutionPointHull z u
    orderOf t = 2 ∧ t ∈ L ∧
      L ≤ Subgroup.centralizer ({u} : Set G) ∧
      (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal ∧
      fusionStronglyEmbedded (H.subgroupOf L) := by
  let L := localInvolutionPointHull z u
  have hLC := localInvolutionPointHull_le_centralizer z u
  have hN : (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr
      (CFSG.ProperTwoGeneratedCore.local_point_hull_normalized_by_centralizer z u)
  have hescape := original_pair_centralizer_escapes H b hb u t hut hflip
  exact ⟨order_two_of_mem_pointClass h.distinguished_order htclass,
    mem_localInvolutionPointHull htclass hut.symm, hLC, hN,
    h.local_embedding u hu huz hescape⟩

theorem original_local_first_centralizer_index_of_abstract_model
    {F : Type v} [Group F] [Finite F] {Ξ : Type w} [MulAction F Ξ]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hb : b ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2) (huz : Commute u z) (hut : Commute u t)
    (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b)
    (e : localInvolutionPointHull z u ≃* F) (hrank : TwoRankAtLeastTwo F)
    (hdouble : MulAction.IsMultiplyPretransitive F Ξ 2)
    (a₀ b₀ : Ξ) (h₀ : a₀ ≠ b₀)
    (hB : fusionStronglyEmbedded (MulAction.stabilizer F a₀))
    (w₀ : F) (hwa : w₀ • a₀ = b₀) (hwb : w₀ • b₀ = a₀)
    (T₀ : Subgroup F)
    (hT₀ : (T₀ : Set F) = {y | y • a₀ = a₀ ∧ y • b₀ = b₀})
    (hcyclic : IsCyclic T₀) (hodd : Odd (Nat.card T₀))
    (hinv : ∀ y ∈ T₀, rightConjugateElem y w₀ = y⁻¹) :
    let L := localInvolutionPointHull z u
    let D := rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H b
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    let T := L ⊓ D
    IsCyclic T ∧ Nat.card T = Nat.card T₀ ∧
      (∀ y ∈ T, rightConjugateElem y t = y⁻¹) ∧
      involutionOrbit A t = involutionOrbit T t ∧
      (∀ d ∈ A, ∃ c ∈ C, ∃ y ∈ T, d = c * y) ∧
      (A : Set G) = (C : Set G) * (T : Set G) ∧
      C ⊓ T = ⊥ ∧ C.relIndex A = Nat.card T₀ := by
  obtain ⟨ht, htL, hLC, hN, hP⟩ :=
    original_pair_local_hull_inputs h b hb u t hu huz hut htclass hflip
  have hPbase : fusionStronglyEmbedded
      ((rightCosetStabilizer H (rightCosetMk H 1)).subgroupOf
        (localInvolutionPointHull z u)) := by
    rw [rightCosetStabilizer_base]
    exact hP
  exact original_first_centralizer_index_of_abstract_model H (localInvolutionPointHull z u)
    (rightCosetMk H 1) b hb.symm u t ht htL hflip hLC hN hPbase
      e hrank hdouble a₀ b₀ h₀ hB w₀ hwa hwb T₀ hT₀ hcyclic hodd hinv

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
