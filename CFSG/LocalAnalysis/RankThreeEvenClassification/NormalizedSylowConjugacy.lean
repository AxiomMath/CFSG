module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CentralizerPlaneGeneration

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem normalized_subgroup_action_map_eq {G : Type u} [Group G]
    (actor overgroup : Subgroup G)
    (hovergroupNormalized : actor ≤ Subgroup.normalizer (overgroup : Set G))
    (subgroup : Subgroup overgroup)
    (hnormalized : actor ≤ Subgroup.normalizer (subgroup.map overgroup.subtype : Set G)) :
    letI := normalizedConjugationAction actor overgroup hovergroupNormalized
    ∀ member : actor,
      subgroup.map (MulDistribMulAction.toMonoidHom overgroup member) = subgroup := by
  let : MulDistribMulAction actor overgroup :=
    normalizedConjugationAction actor overgroup hovergroupNormalized
  intro member
  apply Subgroup.map_injective overgroup.subtype_injective
  rw [Subgroup.map_map]
  have hcompose : overgroup.subtype.comp (MulDistribMulAction.toMonoidHom overgroup member) =
      (MulAut.conj (member : G)).toMonoidHom.comp overgroup.subtype := by
    ext element
    rfl
  rw [hcompose, ← Subgroup.map_map]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormalized member.property)

theorem exists_centralizing_conjugator_of_normalized_sylows
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (sylowPrime : ℕ) (hsylowPrime : sylowPrime.Prime)
    (actor overgroup : Subgroup G) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card overgroup)
    (hovergroupNormalized : actor ≤ Subgroup.normalizer (overgroup : Set G))
    (first second : Sylow sylowPrime overgroup)
    (hfirstNormalized : actor ≤ Subgroup.normalizer ((first : Subgroup overgroup).map overgroup.subtype : Set G))
    (hsecondNormalized : actor ≤ Subgroup.normalizer ((second : Subgroup overgroup).map overgroup.subtype : Set G)) :
    ∃ conjugator ∈ overgroup ⊓ Subgroup.centralizer (actor : Set G),
      ((first : Subgroup overgroup).map overgroup.subtype).map
        (MulAut.conj conjugator).toMonoidHom = (second : Subgroup overgroup).map overgroup.subtype := by
  let : MulDistribMulAction actor overgroup :=
    normalizedConjugationAction actor overgroup hovergroupNormalized
  obtain ⟨conjugator, hfixed, hconjugate⟩ := exists_fixed_conjugator_of_invariant_sylows
    prime hprime hpgroup hcomplement sylowPrime hsylowPrime first second
      (normalized_subgroup_action_map_eq actor overgroup hovergroupNormalized first hfirstNormalized)
      (normalized_subgroup_action_map_eq actor overgroup hovergroupNormalized second hsecondNormalized)
  refine ⟨conjugator, ⟨conjugator.property, ?_⟩, ?_⟩
  · apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have heq := congrArg (fun value : overgroup => (value : G)) (hfixed ⟨member, hmember⟩)
    change member * (conjugator : G) * member⁻¹ = conjugator at heq
    have hmul := congrArg (fun value : G => value * member) heq
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  · have hmapped := congrArg (fun subgroup : Subgroup overgroup => subgroup.map overgroup.subtype) hconjugate
    rw [Subgroup.map_map] at hmapped
    rw [Subgroup.map_map]
    have hcompose : (MulAut.conj (conjugator : G)).toMonoidHom.comp overgroup.subtype =
        overgroup.subtype.comp (MulAut.conj conjugator).toMonoidHom := by
      ext element
      rfl
    rw [hcompose]
    exact hmapped

end CFSG.RankThreeEvenClassification.Helpers
