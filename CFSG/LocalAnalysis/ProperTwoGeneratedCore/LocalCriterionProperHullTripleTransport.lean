module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOddCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFreeFixedPoints

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree

universe u

variable {G : Type u} [Group G]

theorem properHull_point_stabilizer_right_conjugate
    (H : Subgroup G) (alpha : pointRightCosetSpace H) (g : G) :
    rightConjugate (rightCosetStabilizer H alpha) g =
      rightCosetStabilizer H (pointRightCosetMul H alpha g) := by
  ext x
  change x ∈ (rightCosetStabilizer H alpha).map (MulAut.conj g⁻¹).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]
  rw [mem_point_right_stabilizer_iff, mem_point_right_stabilizer_iff]
  constructor
  · intro hx
    calc
      pointRightCosetMul H (pointRightCosetMul H alpha g) x =
          pointRightCosetMul H alpha (g * x) := pointRightCosetMul_mul H alpha g x
      _ = pointRightCosetMul H (pointRightCosetMul H alpha (g * x * g⁻¹)) g := by
        rw [pointRightCosetMul_mul]
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = pointRightCosetMul H alpha g := by rw [hx]
  · intro hx
    have hh := congrArg (fun beta : pointRightCosetSpace H =>
      pointRightCosetMul H beta g⁻¹) hx
    simpa only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one] using hh

theorem properHull_element_centralizer_right_conjugate (z g : G) :
    rightConjugate (Subgroup.centralizer ({z} : Set G)) g =
      Subgroup.centralizer ({rightConjugateElem z g} : Set G) := by
  ext x
  change x ∈ (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have hh := (show Commute (g * x * g⁻¹) z from hx).conj g⁻¹
    simpa only [rightConjugateElem, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hh.eq
  · intro hx
    have hh := (show Commute x (rightConjugateElem z g) from hx).conj g
    simpa only [rightConjugateElem, mul_assoc, mul_inv_cancel_left,
      mul_inv_cancel, mul_one] using hh.eq

theorem properHull_triple_stabilizer_right_conjugate
    (H : Subgroup G) (r g : G) (alpha delta : pointRightCosetSpace H) :
    rightConjugate
      ((rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H delta) ⊓
        rightCosetStabilizer H (pointRightCosetMul H delta r)) g =
      (rightCosetStabilizer H (pointRightCosetMul H alpha g) ⊓
        rightCosetStabilizer H (pointRightCosetMul H delta g)) ⊓
        rightCosetStabilizer H (pointRightCosetMul H
          (pointRightCosetMul H delta g) (rightConjugateElem r g)) := by
  change ((rightCosetStabilizer H alpha ⊓ rightCosetStabilizer H delta) ⊓
    rightCosetStabilizer H (pointRightCosetMul H delta r)).map
      (MulAut.conj g⁻¹).toMonoidHom = _
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective]
  change (rightConjugate (rightCosetStabilizer H alpha) g ⊓
    rightConjugate (rightCosetStabilizer H delta) g) ⊓
    rightConjugate (rightCosetStabilizer H (pointRightCosetMul H delta r)) g = _
  rw [properHull_point_stabilizer_right_conjugate,
    properHull_point_stabilizer_right_conjugate,
    properHull_point_stabilizer_right_conjugate]
  have hact : pointRightCosetMul H (pointRightCosetMul H delta r) g =
      pointRightCosetMul H (pointRightCosetMul H delta g) (rightConjugateElem r g) := by
    rw [pointRightCosetMul_mul, pointRightCosetMul_mul]
    simp only [rightConjugateElem, mul_assoc, mul_inv_cancel_left]
  rw [hact]

variable [Finite G]

theorem properHull_distinguished_triple_of_base
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hbase : ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      triplePointStabilizer H z beta =
        pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G)) :
    distinguishedTripleCentralization H z := by
  intro r hr epsilon delta hfix hdelta
  obtain ⟨g, rfl⟩ := hr
  have hclassfix := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨_, _, huniq⟩ := hclassfix (rightConjugateElem z g) ⟨g, rfl⟩
  have hepsilon : epsilon = rightCosetMk H g :=
    (huniq epsilon hfix).trans (huniq _ (point_class_conjugate_fixed_rightCoset h g)).symm
  have hbaseg : pointRightCosetMul H (rightCosetMk H 1) g = epsilon := by
    rw [pointRightCosetMul_eq_translate, rightCosetTranslate_mk, one_mul, ← hepsilon]
  let delta0 := pointRightCosetMul H delta g⁻¹
  have hreturn : pointRightCosetMul H delta0 g = delta := by
    dsimp only [delta0]
    rw [pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one]
  have hdelta0 : delta0 ≠ rightCosetMk H 1 := by
    intro heq
    apply hdelta
    rw [← hreturn, heq, hbaseg]
  have hbase' :
      (rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H delta0) ⊓
        rightCosetStabilizer H (pointRightCosetMul H delta0 z) =
      (rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H delta0) ⊓
        Subgroup.centralizer ({z} : Set G) := by
    rw [pointRightCosetMul_eq_translate]
    exact hbase delta0 hdelta0
  have hh := congrArg (fun A : Subgroup G => rightConjugate A g) hbase'
  rw [properHull_triple_stabilizer_right_conjugate] at hh
  change _ = ((rightCosetStabilizer H (rightCosetMk H 1) ⊓
    rightCosetStabilizer H delta0) ⊓ Subgroup.centralizer ({z} : Set G)).map
      (MulAut.conj g⁻¹).toMonoidHom at hh
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective] at hh
  change _ = (rightConjugate (rightCosetStabilizer H (rightCosetMk H 1)) g ⊓
    rightConjugate (rightCosetStabilizer H delta0) g) ⊓
    rightConjugate (Subgroup.centralizer ({z} : Set G)) g at hh
  rw [properHull_point_stabilizer_right_conjugate,
    properHull_point_stabilizer_right_conjugate,
    properHull_element_centralizer_right_conjugate, hbaseg, hreturn] at hh
  exact hh

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
