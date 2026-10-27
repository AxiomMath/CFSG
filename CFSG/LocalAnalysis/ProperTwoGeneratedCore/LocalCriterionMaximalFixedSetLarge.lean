module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSetTransitivity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem locally_maximal_large_fixed_set_class_normalizer_point
    {H P : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (T : Sylow 2 G) (hzT : z ∈ (T : Subgroup G))
    (hzcenter : (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G))
    (p : ℕ) (hp : p.Prime) (hP : IsPGroup p P) (hPH : P ≤ H)
    (hmax : IsLocallyMaximalTwoPointPrime H p P)
    (hfixed : 3 ≤ Nat.card (pointFixedSet H P)) :
    ∃ r ∈ involutionPointClass z, r ∈ Subgroup.normalizer (P : Set G) ∧ r ∈ H := by
  have hcard : 1 < (pointFixedSet H P).ncard := by
    change 1 < Nat.card (pointFixedSet H P)
    omega
  obtain ⟨b, hb, hbbase⟩ := Set.exists_ne_of_one_lt_ncard hcard (rightCosetMk H 1)
  obtain ⟨s, hs, _, hsP, hmotion⟩ := locally_maximal_base_pair_flip
    h T hzT hzcenter p hp hP hPH hmax b hb hbbase
  have hglobal := locally_maximal_is_globally_maximal h T hzT hzcenter p hp hP hPH hmax
  have hmotionmax : IsMaximalPrimeMotion H z p P := by
    intro Q hQ hPQ hQfixed _
    exact (ne_of_gt hPQ) (hglobal Q hQ hPQ.le (by omega))
  obtain ⟨a, ha, hsa⟩ := local_involution_point_maximal_prime_fixed_point
    H z h T hzT hzcenter p hp P hP s hs hsP hfixed hmotion hmotionmax
  have hbase : rightCosetMk H 1 ∈ pointFixedSet H P := by
    apply (mem_pointFixedSet_iff H P _).mpr
    rwa [rightCosetStabilizer_base]
  obtain ⟨n, hn, hna⟩ := locally_maximal_normalizer_transitive
    h T hzT hzcenter p hp hP hPH hmax a ha (rightCosetMk H 1) hbase
  let N := Subgroup.normalizer (P : Set G)
  refine ⟨rightConjugateElem s n, pointClass_right_conjugate_mem hs n,
    N.mul_mem (N.mul_mem (N.inv_mem hn) hsP) hn, ?_⟩
  have hh := point_right_fixed_conjugate hsa n
  rw [hna] at hh
  exact (point_right_base_fixed_iff H _).mp hh

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
