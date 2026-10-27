module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCount
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityNative

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

universe u

variable {G : Type u} [Group G] [Finite G]

attribute [local instance] pointRightCosetOppositeMulAction

theorem original_fixed_set_geometry_and_class_count
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hfaithful : ∀ g : G,
      (∀ a : pointRightCosetSpace H, pointRightCosetMul H a g = a) → g = 1)
    (hdouble : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (hodd : Odd (Nat.card (pointRightCosetSpace H)))
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (u t : G) (hu : orderOf u = 2)
    (huC : u ∈ pairPointStabilizer H beta ⊓ Subgroup.centralizer ({t} : Set G))
    (ht : t ∈ rightPairFlipFiber H z beta)
    (hcentralizer : ∀ a b c d : pointRightCosetSpace H,
      pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
      pointRightCosetMul H c u = c → pointRightCosetMul H d u = d →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) :
    let n := Nat.card (pointRightCosetSpace H)
    let k := Nat.card {a : pointRightCosetSpace H // pointRightCosetMul H a u = a}
    let D := pairPointStabilizer H beta
    let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
    3 ≤ k ∧ k < n ∧ Odd k ∧ Nat.card V = 4 ∧ IsElementaryAbelian 2 V ∧
      involutionPointClass u ≠ involutionPointClass z ∧
      Disjoint (involutionPointClass u) (involutionPointClass z) ∧
      (Nat.card (involutionPointClass u) : ℚ) =
        (n : ℚ) * ((n : ℚ) - 1) *
          (Subgroup.centralizer ({u} : Set G)).relIndex D /
          ((k : ℚ) * ((k : ℚ) - 1)) := by
  have hmem := original_pair_centralizer_mem H beta u t huC
  have hbounds := original_pair_involution_fixed_set_bounds
    H hfaithful hodd beta hbeta u hu hmem.1
  have htorder := order_two_of_mem_pointClass h.distinguished_order ht.1
  have hut := pair_stabilizer_element_ne_flip beta hbeta ht u hmem.1
  have hV := generated_commuting_involutions_elementary u t hu htorder hut hmem.2
  have huz := pair_stabilizer_not_distinguished h beta hbeta u hmem.1
  have ha : rightCosetMk H 1 ∈ fixedSet u :=
    (mem_point_right_stabilizer_iff H _ u).mp hmem.1.1
  have hb : beta ∈ fixedSet u :=
    (mem_point_right_stabilizer_iff H beta u).mp hmem.1.2
  have hcount := full_fixed_pair_rational_class_count hdouble u hcentralizer
    (rightCosetMk H 1) beta ha hb hbeta.symm
  rw [original_native_full_class, original_native_pair_stabilizer] at hcount
  exact ⟨hbounds.1, hbounds.2.1, hbounds.2.2, hV.1, hV.2,
    full_point_classes_ne u z huz, full_point_classes_disjoint u z huz, hcount⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
