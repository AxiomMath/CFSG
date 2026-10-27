module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct

public section

open scoped Pointwise

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem thetaPlaneIntersection_le_centralizer {G : Type u} [Group G]
    (prime : ℕ) (plane : Subgroup G) :
    thetaPlaneIntersection prime plane ≤ Subgroup.centralizer (plane : Set G) := by
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  by_cases hidentity : member = 1
  · rw [hidentity, one_mul, mul_one]
  · have htheta := thetaPlaneIntersection_le prime plane member hmember hidentity helement
    exact (Subgroup.mem_centralizer_singleton_iff.mp (thetaCoreOf_le prime _ htheta)).symm

theorem centralizer_plane_normalizes_intersection {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) :
    Subgroup.centralizer (plane : Set G) ≤
      Subgroup.normalizer (thetaPlaneIntersection prime plane : Set G) := by
  apply normalizes_iInf
  intro element
  apply normalizes_iInf
  intro helement
  apply normalizes_iInf
  intro _
  exact ((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr helement)).trans
    Subgroup.le_normalizer).trans (normalizer_le_normalizer_thetaCoreOf prime hprime _)

theorem thetaPlaneIntersection_le_fixed_theta {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G)
    (element : G) (helement : element ∈ plane) (hne : element ≠ 1) :
    thetaPlaneIntersection prime plane ≤ thetaCoreOf prime (Subgroup.centralizer (plane : Set G)) := by
  have hle := thetaPlaneIntersection_le_centralizer prime plane
  exact normal_solvable_primeComplement_le_thetaCoreOf prime _ _ hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (centralizer_plane_normalizes_intersection prime hprime plane))
    (thetaPlaneIntersection_solvable prime hprime plane element helement hne)
    (thetaPlaneIntersection_prime_complement prime hprime plane element helement hne)

theorem centralizer_plane_normalizes_commutators {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) :
    Subgroup.centralizer (plane : Set G) ≤
      Subgroup.normalizer (thetaPlaneCommutators prime plane : Set G) := by
  apply normalizes_iSup
  intro element
  apply normalizes_iSup
  intro helement
  apply normalizes_iSup
  intro _
  exact normalizes_commutator_of_normalizes_both _ _ _
    (((Subgroup.centralizer_le (Set.singleton_subset_iff.mpr helement)).trans
      Subgroup.le_normalizer).trans (normalizer_le_normalizer_thetaCoreOf prime hprime _))
    (Subgroup.centralizer_le_normalizer _)

theorem centralizer_plane_normalizes_alpha {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) :
    Subgroup.centralizer (plane : Set G) ≤
      Subgroup.normalizer (thetaPlaneAlpha prime plane : Set G) := by
  exact (le_inf (centralizer_plane_normalizes_commutators prime hprime plane)
    (centralizer_plane_normalizes_intersection prime hprime plane)).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem thetaPlaneAlpha_coe_product {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) :
    (thetaPlaneAlpha prime plane : Set G) =
      (thetaPlaneCommutators prime plane : Set G) * (thetaPlaneIntersection prime plane : Set G) := by
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
    ((thetaPlaneIntersection_le_centralizer prime plane).trans
      (centralizer_plane_normalizes_commutators prime hprime plane))

end CFSG.RankThreeEvenClassification.Helpers
