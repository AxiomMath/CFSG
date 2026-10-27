module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityFixedSet
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityGeometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerAction
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerCentralizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

universe u

variable {G : Type u} [Group G] [Finite G]

theorem no_two_rank_of_original_four_group_exclusion
    (D : Subgroup G)
    (hno : ∀ E : Subgroup D, IsElementaryAbelian 2 E → Nat.card E ≠ 4) :
    ¬ TwoRankAtLeastTwo D := by
  rintro ⟨E, hcard, hsq⟩
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hdvd : Monoid.exponent E ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  have hexp : Monoid.exponent E = 2 :=
    (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd).resolve_left
      (Nat.ne_of_gt Monoid.one_lt_exponent)
  let : IsKleinFour E := ⟨hcard, hexp⟩
  have helem : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := hdvd }
  exact hno E helem hcard

theorem no_two_rank_subgroupOf (D K : Subgroup G) (hDK : D ≤ K)
    (hno : ¬ TwoRankAtLeastTwo D) :
    ¬ TwoRankAtLeastTwo (D.subgroupOf K) := by
  intro hfour
  let e : D.subgroupOf K ≃* D := Subgroup.subgroupOfEquivOfLe hDK
  exact hno (CFSG.BenderSuzuki.twoRankAtLeastTwo_of_injective
    e.toMonoidHom e.injective hfour)

theorem original_pair_involution_fixed_set_bounds
    (H : Subgroup G)
    (hfaithful : ∀ g : G,
      (∀ a : pointRightCosetSpace H, pointRightCosetMul H a g = a) → g = 1)
    (hodd : Odd (Nat.card (pointRightCosetSpace H)))
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (u : G) (hu : orderOf u = 2) (huD : u ∈ pairPointStabilizer H beta) :
    3 ≤ Nat.card {a : pointRightCosetSpace H // pointRightCosetMul H a u = a} ∧
      Nat.card {a : pointRightCosetSpace H // pointRightCosetMul H a u = a} <
        Nat.card (pointRightCosetSpace H) ∧
      Odd (Nat.card {a : pointRightCosetSpace H // pointRightCosetMul H a u = a}) := by
  let := pointRightCosetOppositeMulAction H
  have ha : rightAct (rightCosetMk H 1) u = rightCosetMk H 1 :=
    (mem_point_right_stabilizer_iff H _ u).mp huD.1
  have hb : rightAct beta u = beta :=
    (mem_point_right_stabilizer_iff H beta u).mp huD.2
  exact full_fixed_set_bounds hfaithful hodd u hu (rightCosetMk H 1) beta ha hb hbeta.symm

theorem original_two_distinct_flip_classes
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (u t : G) (huD : u ∈ pairPointStabilizer H beta)
    (ht : t ∈ involutionPointClass z)
    (htwo : ∀ v : G, orderOf v = 2 →
      v ∈ involutionPointClass u ∨ v ∈ involutionPointClass z) :
    Disjoint (involutionPointClass u) (involutionPointClass t) ∧
      involutionPointClass t = involutionPointClass z ∧
      (∀ v : G, orderOf v = 2 →
        v ∈ involutionPointClass u ∨ v ∈ involutionPointClass t) := by
  have htclass := CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime.pointClass_eq_of_mem ht
  have huz := pair_stabilizer_not_distinguished h beta hbeta u huD
  refine ⟨?_, htclass, ?_⟩
  · rw [htclass]
    exact full_point_classes_disjoint u z huz
  · intro v hv
    rw [htclass]
    exact htwo v hv

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
