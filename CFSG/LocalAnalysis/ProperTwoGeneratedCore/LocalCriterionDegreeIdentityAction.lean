module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerCentralizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

universe u

variable {G : Type u} [Group G]

attribute [local instance] pointRightCosetOppositeMulAction

theorem original_native_pair_stabilizer (H : Subgroup G)
    (beta : pointRightCosetSpace H) :
    rightStabilizer (rightCosetMk H 1) ⊓ rightStabilizer beta =
      pairPointStabilizer H beta := by
  rw [point_rightStabilizer_eq, point_rightStabilizer_eq]
  rfl

theorem original_pair_centralizer_mem
    (H : Subgroup G) (beta : pointRightCosetSpace H) (u t : G)
    (hu : u ∈ pairPointStabilizer H beta ⊓ Subgroup.centralizer ({t} : Set G)) :
    u ∈ pairPointStabilizer H beta ∧ Commute u t := by
  exact ⟨hu.1, Subgroup.mem_centralizer_singleton_iff.mp hu.2⟩

theorem original_native_full_class (s : G) :
    fullClass s = involutionPointClass s :=
  (point_class_eq_full_conjugacy s).symm

theorem original_native_full_swap_set (H : Subgroup G)
    (u : G) (beta : pointRightCosetSpace H) :
    fullFlipSet u (rightCosetMk H 1) beta =
      {v | v ∈ involutionPointClass u ∧
        pointRightCosetMul H (rightCosetMk H 1) v = beta} := by
  rw [fullFlipSet, original_native_full_class]
  rfl

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
