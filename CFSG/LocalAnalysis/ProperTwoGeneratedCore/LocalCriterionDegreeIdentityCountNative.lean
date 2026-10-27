module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityRatioCount

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

theorem original_degree_count_of_proved_swap_orbit
    (H : Subgroup G)
    (hdouble : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (u t : G) (huD : u ∈ pairPointStabilizer H beta)
    (hcentralizer : ∀ a b c d : pointRightCosetSpace H,
      pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
      pointRightCosetMul H c u = c → pointRightCosetMul H d u = d →
      a ≠ b → c ≠ d →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G),
        pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (horbit : {v | v ∈ involutionPointClass u ∧
      pointRightCosetMul H (rightCosetMk H 1) v = beta} =
        conjugacyWithin (pairPointStabilizer H beta) (u * t)) :
    let D := pairPointStabilizer H beta
    let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
    let C := D ⊓ Subgroup.centralizer (V : Set G)
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let B := D ⊓ Subgroup.centralizer ({u * t} : Set G)
    let a : ℚ := (C.relIndex A : ℚ) / C.relIndex B
    let n := Nat.card (pointRightCosetSpace H)
    let k := Nat.card {x : pointRightCosetSpace H // pointRightCosetMul H x u = x}
    (n : ℚ) - k = (k : ℚ) * ((k : ℚ) - 1) * a ∧
      (n : ℚ) - 1 = ((k : ℚ) - 1) * ((k : ℚ) * a + 1) := by
  have ha : rightCosetMk H 1 ∈ fixedSet u :=
    (mem_point_right_stabilizer_iff H _ u).mp huD.1
  have hb : beta ∈ fixedSet u :=
    (mem_point_right_stabilizer_iff H beta u).mp huD.2
  have horbitNative : fullFlipSet u (rightCosetMk H 1) beta =
      conjugacyWithin (rightStabilizer (rightCosetMk H 1) ⊓ rightStabilizer beta)
        (u * t) := by
    rw [original_native_full_swap_set, original_native_pair_stabilizer]
    exact horbit
  have hcount := full_degree_count_of_derived_swap_orbit hdouble u t hcentralizer
    (rightCosetMk H 1) beta ha hb hbeta.symm horbitNative
  dsimp only at hcount ⊢
  rw [original_native_pair_stabilizer] at hcount
  exact hcount

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
