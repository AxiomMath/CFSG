module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizerLocal

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G] [Finite G]

theorem original_triple_sylow_normalizer_every_pair_class_flip
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)) :
    let N := Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G)
    ∀ a b : pointRightCosetSpace H,
      a ∈ pointFixedSet H ((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype) →
      b ∈ pointFixedSet H ((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype) → a ≠ b →
      ∃ n : N, pointRightCosetMul H a (rightConjugateElem z (n : G)) = b ∧
        pointRightCosetMul H b (rightConjugateElem z (n : G)) = a := by
  dsimp only
  let U : Subgroup G := (P : Subgroup (triplePointStabilizer H z beta)).map
    (triplePointStabilizer H z beta).subtype
  let N := Subgroup.normalizer (U : Set G)
  have haction := original_triple_sylow_normalizer_action h S hzS hzcenter hdoubly beta hbeta p hp P hzP
  obtain ⟨s, n, hns, hsbase, hsbeta⟩ := original_triple_sylow_normalizer_base_class_flip
    h S hzS hzcenter hdoubly beta hbeta p hp P hzP beta haction.2.1.2.1 hbeta
  intro a b ha hb hab
  obtain ⟨g, hg, hga, hgb⟩ := haction.2.2.2.2.2.2 (rightCosetMk H 1) beta a b
    haction.2.1.1 haction.2.1.2.1 ha hb hbeta.symm hab
  let gN : N := ⟨g, hg⟩
  have hsconj : rightConjugateElem z ((n * gN : N) : G) =
      rightConjugateElem (s : G) g := by
    rw [Subgroup.coe_mul, ← rightConjugateElem_comp]
    have hh : rightConjugateElem z (n : G) = (s : G) := congrArg Subtype.val hns
    rw [hh]
  refine ⟨n * gN, ?_, ?_⟩
  · rw [hsconj, ← hga]
    have hproduct : g * rightConjugateElem (s : G) g = (s : G) * g := by
      simp only [rightConjugateElem, mul_assoc, mul_inv_cancel_left]
    rw [pointRightCosetMul_mul, hproduct, ← pointRightCosetMul_mul, hsbase, hgb]
  · rw [hsconj, ← hgb]
    have hproduct : g * rightConjugateElem (s : G) g = (s : G) * g := by
      simp only [rightConjugateElem, mul_assoc, mul_inv_cancel_left]
    rw [pointRightCosetMul_mul, hproduct, ← pointRightCosetMul_mul, hsbeta, hga]

theorem original_triple_sylow_normalizer_supplied_flip_class_intersection
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hdoubly : ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (P : Sylow p (triplePointStabilizer H z beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (triplePointStabilizer H z beta)).map
        (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G))
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta) :
    (conjugacyWithin (pairPointStabilizer H beta) t ∩
      (Subgroup.normalizer
        (((P : Subgroup (triplePointStabilizer H z beta)).map
          (triplePointStabilizer H z beta).subtype : Subgroup G) : Set G) : Set G)).Nonempty := by
  have haction := original_triple_sylow_normalizer_action h S hzS hzcenter hdoubly beta hbeta p hp P hzP
  obtain ⟨s, n, hns, hsbase, _⟩ := original_triple_sylow_normalizer_base_class_flip
    h S hzS hzcenter hdoubly beta hbeta p hp P hzP beta haction.2.1.2.1 hbeta
  have hsclass : (s : G) ∈ involutionPointClass z := ⟨(n : G), congrArg Subtype.val hns⟩
  have hsfiber : (s : G) ∈ rightPairFlipFiber H z beta :=
    ⟨hsclass, (pointRightCosetMul_eq_translate H _ _).symm.trans hsbase⟩
  refine ⟨(s : G), ?_, s.property⟩
  rw [← pair_flip_fiber_eq_stabilizer_class h S hzS hzcenter hbeta ht]
  exact hsfiber

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
