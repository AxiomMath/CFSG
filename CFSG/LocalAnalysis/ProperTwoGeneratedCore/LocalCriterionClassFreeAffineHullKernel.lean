module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullFixedPoints
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullImage
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullQuotient

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine

variable {G : Type*} [Group G] [Finite G]

theorem hull_centralizer_le_original_pointwise_kernel
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (Delta : Set (pointRightCosetSpace H)) (u : G) (L : Subgroup G)
    (huDelta : ∀ a ∈ Delta, pointRightCosetMul H a u = a)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hr : ∃ r ∈ L, r ∈ involutionPointClass z)
    (htrans : ∀ a b : pointRightCosetSpace H,
      pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
      ∃ l ∈ L, pointRightCosetMul H a l = b) :
    Subgroup.centralizer (L : Set G) ≤ pointwiseRightStabilizer H Delta := by
  intro j hj
  rw [mem_pointwiseRightStabilizer]
  exact hull_centralizer_fixes_original_subset h Delta u L huDelta hLC hr htrans j hj

omit [Finite G] in
theorem hull_normalizer_conjugation_kernel
    (K L : Subgroup G) (u : G)
    (hJ : Subgroup.centralizer (L : Set G) ≤ K)
    (hEL : Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (L : Set G)) :
    (hullConjugationHom L
      (Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) hEL).ker =
      (Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
        (Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) ∧
    (hullConjugationHom L
      (Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({u} : Set G)) hEL).ker.map
        (Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({u} : Set G)).subtype =
      Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({u} : Set G) := by
  let E := Subgroup.normalizer (K : Set G) ⊓ Subgroup.centralizer ({u} : Set G)
  let J0 := Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({u} : Set G)
  have hJ0E : J0 ≤ E := fun j hj => ⟨Subgroup.le_normalizer (hJ hj.1), hj.2⟩
  have hker : (hullConjugationHom L E hEL).ker = J0.subgroupOf E := by
    rw [hullConjugationHom_ker]
    ext e
    constructor
    · intro he
      exact ⟨he, e.property.2⟩
    · intro he
      exact he.1
  refine ⟨hker, ?_⟩
  rw [hker]
  exact Subgroup.map_subgroupOf_eq_of_le hJ0E

theorem pointwise_kernel_normalizer_image_isSolvable_of_hull
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (W : Subgroup G)
    (hno : ∀ V : Subgroup (pointwiseRightStabilizer H (pointFixedSet H W)),
      CFSG.Open.IsElemAbelian 2 V → Nat.card V ≠ 4)
    (hclassfree : involutionPointClass z ∩ (Subgroup.normalizer
      (pointwiseRightStabilizer H (pointFixedSet H W) : Set G) : Set G) = ∅)
    (u : G) (huK : u ∈ pointwiseRightStabilizer H (pointFixedSet H W))
    (hu : orderOf u = 2) (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal)
    (hr : ∃ r ∈ L, r ∈ involutionPointClass z)
    (hLclass : ∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z)
    (htrans : ∀ a b : pointRightCosetSpace H,
      pointRightCosetMul H a u = a → pointRightCosetMul H b u = b →
      ∃ l ∈ L, pointRightCosetMul H a l = b)
    [Group.IsSolvable (outerAutomorphismGroup L)] :
    Group.IsSolvable (pointwiseKernelNormalizerImage H W) := by
  let K := pointwiseRightStabilizer H (pointFixedSet H W)
  let N := Subgroup.normalizer (K : Set G)
  let E := N ⊓ Subgroup.centralizer ({u} : Set G)
  have hJ : Subgroup.centralizer (L : Set G) ≤ K :=
    hull_centralizer_le_original_pointwise_kernel h _ u L
      ((mem_pointwiseRightStabilizer H _ u).mp huK) hLC hr htrans
  have hJ0E : Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer ({u} : Set G) ≤ E :=
    fun j hj => ⟨Subgroup.le_normalizer (hJ hj.1), hj.2⟩
  have hCL : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mp hLnormal
  have hEL : E ≤ Subgroup.normalizer (L : Set G) := inf_le_right.trans hCL
  let chi := hullConjugationHom L E hEL
  let rho := pointwiseKernelNormalizerRepresentation H W
  let rhoE := rho.comp (Subgroup.inclusion (show E ≤ N from inf_le_left))
  let : Group.IsSolvable chi.range := hull_conjugation_image_isSolvable
    z u L E N inf_le_left hEL inf_le_right hLC hJ0E hclassfree hLclass
  have hker : chi.ker ≤ rhoE.ker := by
    intro e he
    have heJ : (e : G) ∈ Subgroup.centralizer (L : Set G) := by
      change e ∈ (hullConjugationHom L E hEL).ker at he
      rw [hullConjugationHom_ker] at he
      exact he
    have heK : (e : G) ∈ K := hJ heJ
    change rho ⟨e, e.property.1⟩ = 1
    apply MonoidHom.mem_ker.mp
    rw [pointwiseKernelNormalizerRepresentation_ker]
    exact heK
  have hsol : Group.IsSolvable rhoE.range := image_isSolvable_of_kernel_le chi rhoE hker
  have hrange : rhoE.range = pointwiseKernelNormalizerImage H W :=
    normalizer_centralizer_representation_ranges_eq K hno u huK hu rho
      (by rw [pointwiseKernelNormalizerRepresentation_ker])
  rw [hrange] at hsol
  exact hsol

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
