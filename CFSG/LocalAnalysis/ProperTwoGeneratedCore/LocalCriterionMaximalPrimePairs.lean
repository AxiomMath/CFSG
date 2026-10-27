module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointSylows
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G]

theorem normalizer_map_automorphism_mem (A : Subgroup G) (t : G)
    (ht : t ∈ Subgroup.normalizer (A : Set G)) (e : G ≃* G) :
    e t ∈ Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup G) : Set G) := by
  exact Subgroup.le_normalizer_map e.toMonoidHom (Subgroup.mem_map_of_mem e.toMonoidHom ht)

theorem sylow_ambient_image_smul (p : ℕ) (B : Subgroup G) (P : Sylow p B) (g : B) :
    (((g • P : Sylow p B) : Subgroup B).map B.subtype) =
      ((P : Subgroup B).map B.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  change ((P : Subgroup B).map (MulAut.conj g).toMonoidHom).map B.subtype = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem base_pair_specified_sylow_flip [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (Q : Sylow p (pairPointStabilizer H beta)) :
    ∃ r ∈ rightPairFlipFiber H z beta,
      r ∈ Subgroup.normalizer
        (((Q : Subgroup (pairPointStabilizer H beta)).map
          (pairPointStabilizer H beta).subtype : Subgroup G) : Set G) ∧
      Nat.card (conjugacyWithin
        ((Q : Subgroup (pairPointStabilizer H beta)).map
          (pairPointStabilizer H beta).subtype) r) =
        p ^ (Nat.card (conjugacyWithin H z)).factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  have : Nonempty (conjugacyWithin H z) :=
    ⟨⟨z, ⟨1, by simp only [Subgroup.coe_one, inv_one, one_mul, mul_one]⟩⟩⟩
  have hfiber : Nat.card (rightPairFlipFiber H z beta) ≠ 0 := by
    rw [(involution_point_uniform_pair_flips h beta hbeta).1]
    exact Nat.card_pos.ne'
  have : Nonempty (rightPairFlipFiber H z beta) := (Nat.card_ne_zero.mp hfiber).1
  let t := (Classical.choice this : rightPairFlipFiber H z beta)
  obtain ⟨P, hPnorm⟩ := pair_stabilizer_invariant_sylow_exists h S hzS hzcenter hbeta
    t.property p hp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (pairPointStabilizer H beta) P Q
  let r := rightConjugateElem t.val (g : G)⁻¹
  have hr : r ∈ rightPairFlipFiber H z beta :=
    pair_group_conjugate_flip_mem h.distinguished_order hbeta t.property t.property
      (pairPointStabilizer_le_pairFlipGroup H beta t.val
        ((pairPointStabilizer H beta).inv_mem g.property))
  refine ⟨r, hr, ?_, ?_⟩
  · have hmap : ((P : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype).map (MulAut.conj (g : G)).toMonoidHom =
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype := by
      rw [← sylow_ambient_image_smul, hg]
    have hn := normalizer_map_automorphism_mem _ t.val hPnorm (MulAut.conj (g : G))
    rw [hmap] at hn
    simpa only [r, rightConjugateElem, MulAut.conj_apply, inv_inv] using hn
  · apply pair_invariant_sylow_flip_class_card h S hzS hzcenter hbeta hr p hp Q
    have hmap : ((P : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype).map (MulAut.conj (g : G)).toMonoidHom =
      (Q : Subgroup (pairPointStabilizer H beta)).map
        (pairPointStabilizer H beta).subtype := by
      rw [← sylow_ambient_image_smul, hg]
    have hn := normalizer_map_automorphism_mem _ t.val hPnorm (MulAut.conj (g : G))
    rw [hmap] at hn
    simpa only [r, rightConjugateElem, MulAut.conj_apply, inv_inv] using hn

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
