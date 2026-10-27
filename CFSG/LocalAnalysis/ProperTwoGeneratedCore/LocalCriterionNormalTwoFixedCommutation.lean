module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem odd_inf_two_eq_bot [Finite G] (A Q : Subgroup G)
    (hA : Odd (Nat.card A)) (hQ : IsPGroup 2 Q) : A ⊓ Q = ⊥ := by
  obtain ⟨k, hk⟩ := isPGroup_iff_card_dvd_pow.mp hQ
  exact (Subgroup.disjoint_of_coprime_natCard
    (Nat.Coprime.of_dvd_right hk (hA.coprime_two_right.pow_right k))).eq_bot

theorem normal_two_normalizing_odd_centralizes [Finite G]
    (H Q A : Subgroup G) (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hAH : A ≤ H) (hAodd : Odd (Nat.card A))
    (r : G) (hrQ : r ∈ Q) (hrA : r ∈ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.centralizer ({r} : Set G) := by
  have hQconj := (Subgroup.normal_subgroupOf_iff hQH).mp hQnormal
  have hinter := odd_inf_two_eq_bot A Q hAodd hQtwo
  intro a ha
  have hcommA : ⁅r, a⁆ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp hrA a).mp ha) (A.inv_mem ha)
  have hcommQ : ⁅r, a⁆ ∈ Q := by
    have hh := Q.mul_mem hrQ (hQconj r⁻¹ a (Q.inv_mem hrQ) (hAH ha))
    simpa only [commutatorElement_def, mul_assoc] using hh
  have hone : ⁅r, a⁆ = 1 := by
    have hh : ⁅r, a⁆ ∈ A ⊓ Q := ⟨hcommA, hcommQ⟩
    rw [hinter] at hh
    exact hh
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_commute.mp hone).symm.eq

theorem right_conjugate_normal_subgroupOf (H Q : Subgroup G)
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal) (g : G) :
    ((rightConjugate Q g).subgroupOf (rightConjugate H g)).Normal := by
  have hnorm : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mp hQnormal
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hQH)).mpr
  rw [← Subgroup.map_equiv_normalizer_eq Q (MulAut.conj g⁻¹)]
  exact Subgroup.map_mono hnorm

theorem right_conjugate_is_two_group (Q : Subgroup G) (hQ : IsPGroup 2 Q) (g : G) :
    IsPGroup 2 (rightConjugate Q g) := hQ.map (MulAut.conj g⁻¹).toMonoidHom

theorem point_class_in_point_subgroup_mem_normal
    {H Q : Subgroup G} {z r : G} (h : InvolutionPointLocalEmbedding H z)
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal) (hzQ : z ∈ Q)
    (hrclass : r ∈ involutionPointClass z) (hrH : r ∈ H) : r ∈ Q := by
  obtain ⟨g, rfl⟩ := hrclass
  have hgH := (pointClass_conjugate_mem_iff h g).mp hrH
  have hQconj := (Subgroup.normal_subgroupOf_iff hQH).mp hQnormal
  simpa only [rightConjugateElem, inv_inv] using hQconj z g⁻¹ hzQ (H.inv_mem hgH)

theorem point_class_fixed_mem_right_conjugate [Finite G]
    {H Q : Subgroup G} {z r : G} (h : InvolutionPointLocalEmbedding H z)
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal) (hzQ : z ∈ Q)
    (g : G) (hrclass : r ∈ involutionPointClass z)
    (hrfixed : pointRightCosetMul H (rightCosetMk H g) r = rightCosetMk H g) :
    r ∈ rightConjugate Q g := by
  have hrHg : r ∈ rightConjugate H g := by
    rw [← rightCosetStabilizer_mk]
    exact (mem_point_right_stabilizer_iff H _ r).mpr hrfixed
  have hrbackH : rightConjugateElem r g⁻¹ ∈ H := by
    simpa only [rightConjugateElem, inv_inv] using
      (CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow.mem_right_conjugate_iff H g r).mp
        hrHg
  have hrbackclass : rightConjugateElem r g⁻¹ ∈ involutionPointClass z := by
    obtain ⟨a, rfl⟩ := hrclass
    exact ⟨a * g⁻¹, (rightConjugateElem_comp z a g⁻¹).symm⟩
  have hrbackQ := point_class_in_point_subgroup_mem_normal
    h hQH hQnormal hzQ hrbackclass hrbackH
  apply (CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow.mem_right_conjugate_iff Q g r).mpr
  simpa only [rightConjugateElem, inv_inv] using hrbackQ

theorem normal_two_at_every_point [Finite G]
    {H Q : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q) (gamma : pointRightCosetSpace H) :
    ∃ Qgamma : Subgroup G, Qgamma ≤ rightCosetStabilizer H gamma ∧
      (Qgamma.subgroupOf (rightCosetStabilizer H gamma)).Normal ∧ IsPGroup 2 Qgamma ∧
      ∀ r ∈ involutionPointClass z,
        pointRightCosetMul H gamma r = gamma → r ∈ Qgamma := by
  refine Quotient.inductionOn gamma ?_
  intro g
  refine ⟨rightConjugate Q g, ?_, ?_, right_conjugate_is_two_group Q hQtwo g, ?_⟩
  · change rightConjugate Q g ≤ rightCosetStabilizer H (rightCosetMk H g)
    rw [rightCosetStabilizer_mk]
    exact Subgroup.map_mono hQH
  · change ((rightConjugate Q g).subgroupOf
      (rightCosetStabilizer H (rightCosetMk H g))).Normal
    rw [rightCosetStabilizer_mk]
    exact right_conjugate_normal_subgroupOf H Q hQH hQnormal g
  · intro r hr hrfixed
    exact point_class_fixed_mem_right_conjugate h hQH hQnormal hzQ g hr hrfixed

theorem odd_subgroup_at_class_fixed_point_centralizes [Finite G]
    {H Q A : Subgroup G} {z r : G} (h : InvolutionPointLocalEmbedding H z)
    (hQH : Q ≤ H) (hQnormal : (Q.subgroupOf H).Normal)
    (hQtwo : IsPGroup 2 Q) (hzQ : z ∈ Q) (hAodd : Odd (Nat.card A))
    (hrclass : r ∈ involutionPointClass z) (hrA : r ∈ Subgroup.normalizer (A : Set G))
    (gamma : pointRightCosetSpace H) (hgamma : gamma ∈ pointFixedSet H A)
    (hrfixed : pointRightCosetMul H gamma r = gamma) :
    A ≤ Subgroup.centralizer ({r} : Set G) := by
  obtain ⟨Qgamma, hQgH, hQgnormal, hQgtwo, hclass⟩ :=
    normal_two_at_every_point h hQH hQnormal hQtwo hzQ gamma
  exact normal_two_normalizing_odd_centralizes
    (rightCosetStabilizer H gamma) Qgamma A hQgH hQgnormal hQgtwo
    ((mem_pointFixedSet_iff H A gamma).mp hgamma) hAodd r (hclass r hrclass hrfixed) hrA

end CFSG.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixed
