module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorParameter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPair

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

universe u v w

variable {G : Type u} [Group G] [Finite G]

theorem model_every_point_stabilizer_strongly_embedded
    {F : Type v} [Group F] [Finite F] {Ξ : Type w} [MulAction F Ξ]
    (htrans : MulAction.IsPretransitive F Ξ) (a : Ξ)
    (ha : fusionStronglyEmbedded (MulAction.stabilizer F a)) (b : Ξ) :
    fusionStronglyEmbedded (MulAction.stabilizer F b) := by
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq a b
  rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact ha.map_mulEquiv (MulAut.conj g)

theorem original_local_first_index_and_parameter_of_full_model_pair
    {F : Type v} [Group F] [Finite F] {Ξ : Type w}
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hb : b ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2) (huz : Commute u z) (hut : Commute u t)
    (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b)
    (e : localInvolutionPointHull z u ≃* F)
    (rho : F →* Equiv.Perm Ξ) (aB : Ξ) (B : Subgroup F)
    (q : ℕ) (hq : 1 ≤ q) (hqodd : Odd (q - 1))
    (hmodel : FullModelPointPair rho aB B q) :
    let L := localInvolutionPointHull z u
    let D := rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H b
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    let T := L ⊓ D
    IsCyclic T ∧ Nat.card T = q - 1 ∧
      (∀ y ∈ T, rightConjugateElem y t = y⁻¹) ∧
      involutionOrbit A t = involutionOrbit T t ∧
      (∀ d ∈ A, ∃ c ∈ C, ∃ y ∈ T, d = c * y) ∧
      (A : Set G) = (C : Set G) * (T : Set G) ∧
      C ⊓ T = ⊥ ∧ C.relIndex A = q - 1 ∧
      q = Nat.card ↥(({1} : Set G) ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
          (H : Set G))) := by
  let : MulAction F Ξ := MulAction.compHom Ξ rho
  obtain ⟨hB, hrank, hSE, hdouble, hcount, a₀, b₀, w₀, T₀,
    h₀, hwa, hwb, hT₀, hcyclic, hTcard, hinvert⟩ := hmodel
  have htrans : MulAction.IsPretransitive F Ξ := by
    let := hdouble
    exact MulAction.isPretransitive_of_is_two_pretransitive
  have hBaB : fusionStronglyEmbedded (MulAction.stabilizer F aB) := hB ▸ hSE
  have hBa₀ := model_every_point_stabilizer_strongly_embedded htrans aB hBaB a₀
  have hcountB : Nat.card {x : F // x ∈ MulAction.stabilizer F aB ∧ IsInvolution x} =
      q - 1 := hB ▸ hcount
  have hTodd : Odd (Nat.card T₀) := hTcard.symm ▸ hqodd
  have hindex := original_local_first_centralizer_index_of_abstract_model
    h b hb u t hu huz hut htclass hflip e hrank hdouble a₀ b₀ h₀ hBa₀
      w₀ hwa hwb T₀ hT₀ hcyclic hTodd hinvert
  obtain ⟨hTC, hcard, hinv, horbit, hfactor, hproduct, hinter, hi⟩ := hindex
  have hparameter := original_local_point_parameter_of_abstract_model h b hb u t
    hu huz hut htclass hflip e hrank htrans aB hBaB q hq hcountB
  exact ⟨hTC, hcard.trans hTcard, hinv, horbit, hfactor, hproduct, hinter,
    hi.trans hTcard, hparameter⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
