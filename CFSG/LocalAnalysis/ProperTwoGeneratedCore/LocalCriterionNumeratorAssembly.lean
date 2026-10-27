module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorOrbit

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

theorem original_first_centralizer_index_of_abstract_model
    {F : Type v} [Group F] [Finite F] {Ξ : Type w} [MulAction F Ξ]
    (H L : Subgroup G) (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (u t : G) (ht : orderOf t = 2) (htL : t ∈ L)
    (hflip : pointRightCosetMul H a t = b)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal)
    (hP : fusionStronglyEmbedded ((rightCosetStabilizer H a).subgroupOf L))
    (e : L ≃* F) (hrank : TwoRankAtLeastTwo F)
    (hdouble : MulAction.IsMultiplyPretransitive F Ξ 2)
    (a₀ b₀ : Ξ) (h₀ : a₀ ≠ b₀)
    (hB : fusionStronglyEmbedded (MulAction.stabilizer F a₀))
    (w₀ : F) (hwa : w₀ • a₀ = b₀) (hwb : w₀ • b₀ = a₀)
    (T₀ : Subgroup F)
    (hT₀ : (T₀ : Set F) = {y | y • a₀ = a₀ ∧ y • b₀ = b₀})
    (hcyclic : IsCyclic T₀) (hodd : Odd (Nat.card T₀))
    (hinv : ∀ y ∈ T₀, rightConjugateElem y w₀ = y⁻¹) :
    let D := rightCosetStabilizer H a ⊓ rightCosetStabilizer H b
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    let T := L ⊓ D
    IsCyclic T ∧ Nat.card T = Nat.card T₀ ∧
      (∀ y ∈ T, rightConjugateElem y t = y⁻¹) ∧
      involutionOrbit A t = involutionOrbit T t ∧
      (∀ d ∈ A, ∃ c ∈ C, ∃ y ∈ T, d = c * y) ∧
      (A : Set G) = (C : Set G) * (T : Set G) ∧
      C ⊓ T = ⊥ ∧ C.relIndex A = Nat.card T₀ := by
  have htrans : MulAction.IsPretransitive F Ξ := by
    let := hdouble
    exact MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨E, f, _, _, hequiv⟩ := original_right_orbit_model_identification
    H L a hP hrank htrans a₀ hB e
  have hb : b ∈ numeratorRightOrbit H L a := ⟨t, htL, hflip⟩
  obtain ⟨hTcyclic, hTcard, hTinvert⟩ := original_right_pair_intersection_data
    H L a b hb hab t ht htL hflip E f hequiv
      hdouble a₀ b₀ h₀ w₀ hwa hwb T₀ hT₀ hcyclic hinv
  have hTodd : Odd (Nat.card (L ⊓
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G)) :=
    hTcard.symm ▸ hodd
  obtain ⟨horbit, hfactor, hproduct, hinter, hindex⟩ :=
    original_pair_first_centralizer_product_index H a b u t ht hflip L
      hLC hLnormal htL hTodd hTinvert
  exact ⟨hTcyclic, hTcard, hTinvert, horbit, hfactor, hproduct, hinter,
    hindex.trans hTcard⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
