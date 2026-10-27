module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorModel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem binary_parameter_predecessor_odd (n : ℕ) (hn : n ≠ 0) :
    Odd (2 ^ n - 1) := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have heven : Even (2 ^ n) := (show Even (2 : ℕ) from by decide).pow_of_ne_zero hn
  exact (Nat.odd_sub' hq).mpr (by simpa using heven)

theorem original_linear_first_index_and_parameter
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hb : b ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2) (huz : Commute u z) (hut : Commute u t)
    (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b)
    {K : Type} [Field K] [Finite K] (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = 2 ^ f)
    (e : localInvolutionPointHull z u ≃* GLAProj (GLASLGroup (Fin 2) K)) :
    let L := localInvolutionPointHull z u
    let D := rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H b
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    let T := L ⊓ D
    IsCyclic T ∧ Nat.card T = 2 ^ f - 1 ∧
      (∀ y ∈ T, rightConjugateElem y t = y⁻¹) ∧
      involutionOrbit A t = involutionOrbit T t ∧
      (∀ d ∈ A, ∃ c ∈ C, ∃ y ∈ T, d = c * y) ∧
      (A : Set G) = (C : Set G) * (T : Set G) ∧
      C ⊓ T = ⊥ ∧ C.relIndex A = 2 ^ f - 1 ∧
      2 ^ f = Nat.card ↥(({1} : Set G) ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
          (H : Set G))) := by
  obtain ⟨_, _, rho, aB, B, _, _, hmodel⟩ :=
    linear_field_model_pair_full f hf hcard
  exact original_local_first_index_and_parameter_of_full_model_pair h b hb
    u t hu huz hut htclass hflip e rho aB B (2 ^ f)
      (Nat.one_le_pow f 2 (by decide))
      (binary_parameter_predecessor_odd f (by omega)) hmodel

theorem original_suzuki_first_index_and_parameter
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (b : pointRightCosetSpace H) (hb : b ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2) (huz : Commute u z) (hut : Commute u t)
    (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = b)
    {K : Type} [Field K] [Finite K] (a : ℕ) (ha : 1 ≤ a)
    (hcard : Nat.card K = 2 ^ (2 * a + 1))
    (e : localInvolutionPointHull z u ≃* GLASzGroup a K) :
    let L := localInvolutionPointHull z u
    let D := rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H b
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let C := D ⊓ Subgroup.centralizer (denominatorFourGroup u t : Set G)
    let T := L ⊓ D
    IsCyclic T ∧ Nat.card T = 2 ^ (2 * a + 1) - 1 ∧
      (∀ y ∈ T, rightConjugateElem y t = y⁻¹) ∧
      involutionOrbit A t = involutionOrbit T t ∧
      (∀ d ∈ A, ∃ c ∈ C, ∃ y ∈ T, d = c * y) ∧
      (A : Set G) = (C : Set G) * (T : Set G) ∧
      C ⊓ T = ⊥ ∧ C.relIndex A = 2 ^ (2 * a + 1) - 1 ∧
      2 ^ (2 * a + 1) = Nat.card ↥(({1} : Set G) ∪
        (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) ∩
          (H : Set G))) := by
  obtain ⟨_, rho, aB, B, _, _, hmodel⟩ :=
    suzuki_field_model_pair_full a ha hcard
  exact original_local_first_index_and_parameter_of_full_model_pair h b hb
    u t hu huz hut htclass hflip e rho aB B (2 ^ (2 * a + 1))
      (Nat.one_le_pow (2 * a + 1) 2 (by decide))
      (binary_parameter_predecessor_odd (2 * a + 1) (by omega)) hmodel

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
