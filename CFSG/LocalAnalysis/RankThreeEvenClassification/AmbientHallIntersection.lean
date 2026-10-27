module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedSylowConjugacy
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantHallIntersection

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem normalized_subgroup_of_action_map_eq {G : Type u} [Group G]
    (actor overgroup : Subgroup G)
    (hovergroupNormalized : actor ≤ Subgroup.normalizer (overgroup : Set G))
    (subgroup : Subgroup overgroup)
    (hinvariant : letI := normalizedConjugationAction actor overgroup hovergroupNormalized
      ∀ member : actor, subgroup.map (MulDistribMulAction.toMonoidHom overgroup member) = subgroup) :
    actor ≤ Subgroup.normalizer (subgroup.map overgroup.subtype : Set G) := by
  let : MulDistribMulAction actor overgroup :=
    normalizedConjugationAction actor overgroup hovergroupNormalized
  intro member hmember
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have heq := congrArg (fun candidate : Subgroup overgroup => candidate.map overgroup.subtype)
    (hinvariant (⟨member, hmember⟩ : actor))
  rw [Subgroup.map_map] at heq
  have hcompose : overgroup.subtype.comp
      (MulDistribMulAction.toMonoidHom overgroup (⟨member, hmember⟩ : actor)) =
      (MulAut.conj member).toMonoidHom.comp overgroup.subtype := by
    ext element
    rfl
  rw [hcompose, ← Subgroup.map_map] at heq
  exact heq

theorem conjugation_action_fixed_iff {G : Type u} [Group G]
    (actor overgroup : Subgroup G)
    (hovergroupNormalized : actor ≤ Subgroup.normalizer (overgroup : Set G)) (element : overgroup) :
    letI := normalizedConjugationAction actor overgroup hovergroupNormalized
    (∀ member : actor, member • element = element) ↔
      (element : G) ∈ Subgroup.centralizer (actor : Set G) := by
  let : MulDistribMulAction actor overgroup :=
    normalizedConjugationAction actor overgroup hovergroupNormalized
  constructor
  · intro hfixed
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmember
    have heq := congrArg (fun value : overgroup => (value : G)) (hfixed ⟨member, hmember⟩)
    change member * (element : G) * member⁻¹ = element at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  · intro hfixed member
    apply Subtype.ext
    change (member : G) * element * (member : G)⁻¹ = element
    have hcommute := Subgroup.mem_centralizer_iff.mp hfixed member member.property
    rw [hcommute, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_greatest_fixed_normalized_primeSetSubgroup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor overgroup : Subgroup G)
    (hpgroup : IsPGroup prime actor)
    (hovergroupNormalized : actor ≤ Subgroup.normalizer (overgroup : Set G))
    (hsolvable : Group.IsSolvable overgroup) (hcomplement : ¬prime ∣ Nat.card overgroup)
    (primes : Set ℕ) :
    ∃ greatest : Subgroup G, greatest ≤ overgroup ∧
      actor ≤ Subgroup.normalizer (greatest : Set G) ∧
      PrimeSetOrder primes (Nat.card greatest) ∧
      overgroup ⊓ Subgroup.centralizer (actor : Set G) ≤ Subgroup.normalizer (greatest : Set G) ∧
      ∀ subgroup : Subgroup G, subgroup ≤ overgroup →
        actor ≤ Subgroup.normalizer (subgroup : Set G) →
        PrimeSetOrder primes (Nat.card subgroup) →
        overgroup ⊓ Subgroup.centralizer (actor : Set G) ≤ Subgroup.normalizer (subgroup : Set G) →
        subgroup ≤ greatest := by
  have : Group.IsSolvable overgroup := hsolvable
  let : MulDistribMulAction actor overgroup :=
    normalizedConjugationAction actor overgroup hovergroupNormalized
  let intersection := invariantHallIntersection (actor := actor) (acted := overgroup) primes
  let greatest := intersection.map overgroup.subtype
  refine ⟨greatest, Subgroup.map_subtype_le intersection,
    normalized_subgroup_of_action_map_eq actor overgroup hovergroupNormalized intersection
      (invariantHallIntersection_invariant primes), ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective overgroup.subtype_injective]
    exact invariantHallIntersection_primeSetOrder prime hprime hpgroup hcomplement primes
  · intro conjugator hconjugator
    let internal : overgroup := ⟨conjugator, hconjugator.1⟩
    have hfixed : ∀ member : actor, member • internal = internal :=
      (conjugation_action_fixed_iff actor overgroup hovergroupNormalized internal).mpr hconjugator.2
    have hnormal := invariantHallIntersection_fixed_normalizes primes internal hfixed
    have heq : intersection.map (MulAut.conj internal).toMonoidHom = intersection :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnormal
    have hmapped := congrArg (fun candidate : Subgroup overgroup => candidate.map overgroup.subtype) heq
    rw [map_conjugate_subgroup_eq] at hmapped
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    exact hmapped
  · intro subgroup hle hnormalized horder hfixedNormalized
    have hrestrictedInvariant := normalized_subgroup_action_map_eq actor overgroup hovergroupNormalized
      (subgroup.subgroupOf overgroup) (by rw [Subgroup.map_subgroupOf_eq_of_le hle]; exact hnormalized)
    have hrestrictedFixedNormalized : ∀ conjugator : overgroup,
        (∀ member : actor, member • conjugator = conjugator) →
          conjugator ∈ Subgroup.normalizer (subgroup.subgroupOf overgroup : Set overgroup) := by
      intro conjugator hfixed
      have hambient := hfixedNormalized ⟨conjugator.property,
        (conjugation_action_fixed_iff actor overgroup hovergroupNormalized conjugator).mp hfixed⟩
      rw [← Subgroup.subgroupOf_normalizer_eq hle]
      exact hambient
    have hrestrictedLe := le_invariantHallIntersection_of_fixed_normalized prime hprime hpgroup
      hcomplement primes (subgroup.subgroupOf overgroup)
        (PrimeSetOrder.subgroupOf primes subgroup overgroup hle horder)
        hrestrictedInvariant hrestrictedFixedNormalized
    have hmapped := Subgroup.map_mono (f := overgroup.subtype) hrestrictedLe
    rw [Subgroup.map_subgroupOf_eq_of_le hle] at hmapped
    exact hmapped

end CFSG.RankThreeEvenClassification.Helpers
