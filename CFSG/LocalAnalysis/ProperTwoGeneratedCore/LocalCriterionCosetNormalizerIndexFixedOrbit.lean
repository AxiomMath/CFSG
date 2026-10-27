module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u

variable {G : Type u} [Group G]

@[expose] def cosetFixedSet (H : Subgroup G) (u : G) : Set (pointRightCosetSpace H) :=
  {omega | pointRightCosetMul H omega u = omega}

theorem cosetFixedSet_eq_zpowers_fixedSet (H : Subgroup G) (u : G) :
    cosetFixedSet H u = pointFixedSet H (Subgroup.zpowers u) := by
  ext omega
  rw [mem_pointFixedSet_iff, Subgroup.zpowers_le]
  exact (mem_point_right_stabilizer_iff H omega u).symm

theorem point_centralizer_preserves_cosetFixedSet (H : Subgroup G) (u a : G)
    (ha : a ∈ Subgroup.centralizer ({u} : Set G))
    {omega : pointRightCosetSpace H} (homega : omega ∈ cosetFixedSet H u) :
    pointRightCosetMul H omega a ∈ cosetFixedSet H u := by
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp ha
  change pointRightCosetMul H (pointRightCosetMul H omega a) u =
    pointRightCosetMul H omega a
  rw [pointRightCosetMul_mul, hcomm, ← pointRightCosetMul_mul, homega]

theorem point_subgroup_preserves_nonbase (H : Subgroup G) (a : G) (ha : a ∈ H)
    {omega : pointRightCosetSpace H} (homega : omega ≠ rightCosetMk H 1) :
    pointRightCosetMul H omega a ≠ rightCosetMk H 1 := by
  intro heq
  have h := congrArg (fun x : pointRightCosetSpace H => pointRightCosetMul H x a⁻¹) heq
  rw [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one,
    (point_right_base_fixed_iff H a⁻¹).mpr (H.inv_mem ha)] at h
  exact homega h

theorem point_subgroup_stabilizer_eq_pair (H A : Subgroup G) (hAH : A ≤ H)
    (beta : pointRightCosetSpace H) :
    letI := pointSubgroupInverseRightAction H A
    MulAction.stabilizer A beta = (pairPointStabilizer H beta).subgroupOf A := by
  let := pointSubgroupInverseRightAction H A
  ext a
  rw [MulAction.mem_stabilizer_iff]
  change pointRightCosetMul H beta a.val⁻¹ = beta ↔ a.val ∈ pairPointStabilizer H beta
  rw [← mem_point_right_stabilizer_iff, (rightCosetStabilizer H beta).inv_mem_iff]
  constructor
  · intro ha
    exact ⟨by rw [rightCosetStabilizer_base]; exact hAH a.property, ha⟩
  · exact fun ha => ha.2

theorem point_centralizer_index_of_full_offBase_orbit (H A : Subgroup G)
    (hAH : A ≤ H) (u : G) (huH : u ∈ H)
    (hAC : A ≤ Subgroup.centralizer ({u} : Set G))
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hbetafix : pointRightCosetMul H beta u = beta)
    (horbit : ∀ omega ∈ cosetFixedSet H u, omega ≠ rightCosetMk H 1 →
      ∃ a : A, pointRightCosetMul H beta (a : G) = omega) :
    (pairPointStabilizer H beta).relIndex A = Nat.card (cosetFixedSet H u) - 1 := by
  let := pointSubgroupInverseRightAction H A
  have hset : MulAction.orbit A beta = cosetFixedSet H u \ {rightCosetMk H 1} := by
    ext omega
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, rfl⟩
      change pointRightCosetMul H beta (a : G)⁻¹ ∈ cosetFixedSet H u ∧
        pointRightCosetMul H beta (a : G)⁻¹ ∉ ({rightCosetMk H 1} : Set _)
      exact ⟨point_centralizer_preserves_cosetFixedSet H u _
          (hAC (A.inv_mem a.property)) hbetafix,
        point_subgroup_preserves_nonbase H _ (hAH (A.inv_mem a.property)) hbeta⟩
    · rintro ⟨hfix, hnonbase⟩
      obtain ⟨a, ha⟩ := horbit omega hfix hnonbase
      refine ⟨a⁻¹, ?_⟩
      change pointRightCosetMul H beta ((a⁻¹ : A) : G)⁻¹ = omega
      simpa only [Subgroup.coe_inv, inv_inv] using ha
  have hbase : rightCosetMk H 1 ∈ cosetFixedSet H u :=
    (point_right_base_fixed_iff H u).mpr huH
  calc
    _ = (MulAction.stabilizer A beta).index := by
      rw [point_subgroup_stabilizer_eq_pair H A hAH beta]
      rfl
    _ = (MulAction.orbit A beta).ncard := MulAction.index_stabilizer A beta
    _ = (cosetFixedSet H u).ncard - 1 := by
      rw [hset, Set.ncard_sdiff_singleton_of_mem hbase]
    _ = Nat.card (cosetFixedSet H u) - 1 := by rw [Nat.card_coe_set_eq]

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
