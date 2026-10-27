module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexFixedOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOrder

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

universe u

variable {G : Type u} [Group G]

theorem original_coset_degree_eq_index (H : Subgroup G) :
    Nat.card (pointRightCosetSpace H) = H.index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)

theorem original_coset_degree_odd [Finite G] {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) : Odd (Nat.card (pointRightCosetSpace H)) := by
  rw [original_coset_degree_eq_index]
  exact local_embedding_index_odd h

theorem original_pair_index_of_double_transitivity (H : Subgroup G)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) :
    (pairPointStabilizer H beta).relIndex H = Nat.card (pointRightCosetSpace H) - 1 := by
  let := pointSubgroupInverseRightAction H H
  have hset : MulAction.orbit H beta = {omega : pointRightCosetSpace H |
      omega ≠ rightCosetMk H 1} := by
    ext omega
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, rfl⟩
      exact point_subgroup_preserves_nonbase H _ (H.inv_mem a.property) hbeta
    · intro homega
      obtain ⟨g, hgbase, hg⟩ := hdoubly (rightCosetMk H 1) beta
        (rightCosetMk H 1) omega hbeta.symm homega.symm
      have hgH := (point_right_base_fixed_iff H g).mp hgbase
      refine ⟨(⟨g, hgH⟩ : H)⁻¹, ?_⟩
      change pointRightCosetMul H beta (((⟨g, hgH⟩ : H)⁻¹ : H) : G)⁻¹ = omega
      simpa only [Subgroup.coe_inv, inv_inv] using hg
  have hcompl : {omega : pointRightCosetSpace H | omega ≠ rightCosetMk H 1} =
      Set.univ \ {rightCosetMk H 1} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
  calc
    _ = (MulAction.stabilizer H beta).index := by
      rw [point_subgroup_stabilizer_eq_pair H H le_rfl beta]
      rfl
    _ = (MulAction.orbit H beta).ncard := MulAction.index_stabilizer H beta
    _ = Nat.card (pointRightCosetSpace H) - 1 := by
      rw [hset, hcompl, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _),
        Set.ncard_univ]

theorem primePower_pair_index_dvd_original_degree [Finite G]
    {p : ℕ} [Fact p.Prime] (H N : Subgroup G) (hNH : N ≤ H)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (Q : Sylow p (pairPointStabilizer H beta))
    (hQ : (Q : Subgroup (pairPointStabilizer H beta)).map
      (pairPointStabilizer H beta).subtype ≤ N)
    (hindex : ∃ e : ℕ, (pairPointStabilizer H beta).relIndex N = p ^ e) :
    (pairPointStabilizer H beta).relIndex N ∣ Nat.card (pointRightCosetSpace H) - 1 := by
  rw [← original_pair_index_of_double_transitivity H beta hbeta hdoubly]
  exact primePower_intersection_index_dvd N (pairPointStabilizer H beta) H hNH
    (pairPointStabilizer_le_point H beta) Q hQ hindex

theorem every_normalizer_sylow_ambient_of_original_degree [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (N : Subgroup G) (hNH : N ≤ H)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (Q : Sylow 2 (pairPointStabilizer H beta))
    (hQ : (Q : Subgroup (pairPointStabilizer H beta)).map
      (pairPointStabilizer H beta).subtype ≤ N)
    (heq : (pairPointStabilizer H beta).relIndex N = Nat.card (pointRightCosetSpace H) - 1)
    (S : Sylow 2 N) :
    ∃ R : Sylow 2 G, (R : Subgroup G) = (S : Subgroup N).map N.subtype := by
  apply supplied_sylow_in_ambient_of_index_eq N (pairPointStabilizer H beta) H hNH
    (pairPointStabilizer_le_point H beta) Q hQ
  · rw [original_pair_index_of_double_transitivity H beta hbeta hdoubly]
    exact heq
  · exact (local_embedding_index_odd h).not_two_dvd_nat

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
