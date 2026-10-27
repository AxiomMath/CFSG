module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCountingInheritance

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

universe u

variable {G : Type u} [Group G]

theorem pointRightCosetMul_eq_translate (H : Subgroup G)
    (gamma : pointRightCosetSpace H) (g : G) :
    pointRightCosetMul H gamma g = rightCosetTranslate H gamma g := by
  refine Quotient.inductionOn gamma ?_
  intro x
  exact pointRightCosetMul_mk H x g

theorem mem_point_right_stabilizer_iff (H : Subgroup G)
    (gamma : pointRightCosetSpace H) (g : G) :
    g ∈ rightCosetStabilizer H gamma ↔ pointRightCosetMul H gamma g = gamma := by
  rw [pointRightCosetMul_eq_translate]
  exact mem_rightCosetStabilizer_iff H gamma g

theorem point_right_base_fixed_iff (H : Subgroup G) (g : G) :
    pointRightCosetMul H (rightCosetMk H 1) g = rightCosetMk H 1 ↔ g ∈ H := by
  rw [← mem_point_right_stabilizer_iff, rightCosetStabilizer_base]

theorem point_right_fixed_conjugate {H : Subgroup G}
    {gamma : pointRightCosetSpace H} {s : G}
    (hfix : pointRightCosetMul H gamma s = gamma) (n : G) :
    pointRightCosetMul H (pointRightCosetMul H gamma n)
      (rightConjugateElem s n) = pointRightCosetMul H gamma n := by
  rw [pointRightCosetMul_mul]
  have hproduct : n * rightConjugateElem s n = s * n := by
    simp only [rightConjugateElem, mul_assoc, mul_inv_cancel_left]
  rw [hproduct, ← pointRightCosetMul_mul, hfix]

theorem invariant_subgroup_mem_normalizer {Y : Subgroup G} {z : G}
    (hYz : rightConjugate Y z = Y) : z ∈ Subgroup.normalizer (Y : Set G) := by
  have hzinv : z⁻¹ ∈ Subgroup.normalizer (Y : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact hYz
  exact (Subgroup.normalizer (Y : Set G)).inv_mem_iff.mp hzinv

theorem normalizer_orbit_point_fixed {H Y : Subgroup G} (hYH : Y ≤ H)
    {a y : G} (ha : a ∈ Subgroup.normalizer (Y : Set G)) (hy : y ∈ Y) :
    pointRightCosetMul H (pointRightCosetMul H (rightCosetMk H 1) a) y =
      pointRightCosetMul H (rightCosetMk H 1) a := by
  have hconj : a * y * a⁻¹ ∈ H := hYH ((Subgroup.mem_normalizer_iff.mp ha y).mp hy)
  calc
    pointRightCosetMul H (pointRightCosetMul H (rightCosetMk H 1) a) y =
        pointRightCosetMul H (rightCosetMk H 1) (a * y) :=
      pointRightCosetMul_mul H _ a y
    _ = pointRightCosetMul H
        (pointRightCosetMul H (rightCosetMk H 1) (a * y * a⁻¹)) a := by
      rw [pointRightCosetMul_mul]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = pointRightCosetMul H (rightCosetMk H 1) a := by
      rw [(point_right_base_fixed_iff H _).mpr hconj]

theorem normalizer_orbit_stabilizer_contains {H Y : Subgroup G} (hYH : Y ≤ H)
    {gamma : pointRightCosetSpace H}
    (horbit : ∃ a : Subgroup.normalizer (Y : Set G),
      pointRightCosetMul H (rightCosetMk H 1) (a : G) = gamma) :
    Y ≤ rightCosetStabilizer H gamma := by
  obtain ⟨a, rfl⟩ := horbit
  intro y hy
  apply (mem_point_right_stabilizer_iff H _ y).mpr
  exact normalizer_orbit_point_fixed hYH a.property hy

theorem subgroup_class_conjugate_mem_point [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (A : Subgroup G) (hzA : z ∈ A) {s : G}
    (hs : s ∈ involutionPointClass z) (hsA : s ∈ A) :
    ∃ a : A, rightConjugateElem s (a : G) ∈ H := by
  by_cases hAH : A ≤ H
  · refine ⟨1, ?_⟩
    simpa only [Subgroup.coe_one, rightConjugateElem, inv_one, one_mul, mul_one]
      using hAH hsA
  · obtain ⟨T, hzT, hztcenter⟩ :=
      (involution_point_subgroup_inheritance h A hzA hAH).2 ⟨S, hzS, hzcenter⟩
    let sA : A := ⟨s, hsA⟩
    have hsorder : orderOf sA = 2 := by
      exact (Subgroup.orderOf_coe sA).symm.trans
        (order_two_of_mem_pointClass h.distinguished_order hs)
    obtain ⟨a, ha⟩ := involution_conjugate_into_sylow T hsorder
    refine ⟨a, point_centralizer_le h ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcomm := Subgroup.mem_center_iff.mp hztcenter
      (⟨rightConjugateElem sA a, ha⟩ : (T : Subgroup A))
    exact congrArg (fun x : (T : Subgroup A) => ((x : A) : G)) hcomm

theorem involution_point_invariant_subgroup_normalizer_fixed_points [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ H) (hYz : rightConjugate Y z = Y)
    {s : G} (hs : s ∈ involutionPointClass z ∩
      (Subgroup.normalizer (Y : Set G) : Set G)) :
    (∃! gamma : pointRightCosetSpace H, pointRightCosetMul H gamma s = gamma) ∧
      ∀ gamma : pointRightCosetSpace H, pointRightCosetMul H gamma s = gamma →
        (∃ a : Subgroup.normalizer (Y : Set G),
          pointRightCosetMul H (rightCosetMk H 1) (a : G) = gamma) ∧
        Y ≤ rightCosetStabilizer H gamma := by
  have hclassfix :=
    ((involution_point_unique_containment_action h.distinguished_mem h.distinguished_order).2
      h.unique_containment).2.1
  refine ⟨hclassfix s hs.1, ?_⟩
  intro gamma hgamma
  have hzN : z ∈ Subgroup.normalizer (Y : Set G) := invariant_subgroup_mem_normalizer hYz
  obtain ⟨n, hn⟩ := subgroup_class_conjugate_mem_point h S hzS hzcenter
    (Subgroup.normalizer (Y : Set G)) hzN hs.1 hs.2
  have hconjclass := pointClass_right_conjugate_mem hs.1 (n : G)
  obtain ⟨delta, _, hdelta⟩ := hclassfix (rightConjugateElem s (n : G)) hconjclass
  have hbase : pointRightCosetMul H (rightCosetMk H 1)
      (rightConjugateElem s (n : G)) = rightCosetMk H 1 :=
    (point_right_base_fixed_iff H _).mpr hn
  have htransport : pointRightCosetMul H gamma (n : G) = rightCosetMk H 1 :=
    (hdelta _ (point_right_fixed_conjugate hgamma (n : G))).trans (hdelta _ hbase).symm
  have horbit : ∃ a : Subgroup.normalizer (Y : Set G),
      pointRightCosetMul H (rightCosetMk H 1) (a : G) = gamma := by
    refine ⟨n⁻¹, ?_⟩
    have hh := congrArg (fun omega : pointRightCosetSpace H =>
      pointRightCosetMul H omega (n : G)⁻¹) htransport
    simpa only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one,
      Subgroup.coe_inv] using hh.symm
  exact ⟨horbit, normalizer_orbit_stabilizer_contains hYH horbit⟩

theorem involution_point_normalizer_fixed_points_subset [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ H) (hYz : rightConjugate Y z = Y) :
    {gamma : pointRightCosetSpace H | ∃ s ∈ involutionPointClass z ∩
        (Subgroup.normalizer (Y : Set G) : Set G), pointRightCosetMul H gamma s = gamma} ⊆
      {gamma : pointRightCosetSpace H | ∀ y ∈ Y, pointRightCosetMul H gamma y = gamma} := by
  rintro gamma ⟨s, hs, hgamma⟩ y hy
  apply (mem_point_right_stabilizer_iff H gamma y).mp
  exact ((involution_point_invariant_subgroup_normalizer_fixed_points
    h S hzS hzcenter Y hYH hYz hs).2 gamma hgamma).2 hy

end CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
