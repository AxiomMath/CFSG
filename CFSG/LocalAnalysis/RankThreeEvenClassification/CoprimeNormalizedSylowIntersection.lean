module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylowContainment
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedSylowConjugacy

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

set_option maxHeartbeats 600000 in
theorem coprime_normalized_sylow_intersection {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor overgroup : Subgroup G)
    (hpgroup : IsPGroup prime actor) (hcomplement : ¬prime ∣ Nat.card overgroup)
    (hovergroupNormalized : actor ≤ Subgroup.normalizer (overgroup : Set G))
    (subgroupPrime : ℕ) (hsubgroupPrime : subgroupPrime.Prime) (sylow : Sylow subgroupPrime overgroup)
    (hsylowNormalized : actor ≤ Subgroup.normalizer
      ((sylow : Subgroup overgroup).map overgroup.subtype : Set G))
    (subgroup : Subgroup G) (hle : subgroup ≤ overgroup)
    (hsubgroupNormalized : actor ≤ Subgroup.normalizer (subgroup : Set G))
    (hfixedNormalized : overgroup ⊓ Subgroup.centralizer (actor : Set G) ≤
      Subgroup.normalizer (subgroup : Set G)) :
    ∃ intersectionSylow : Sylow subgroupPrime subgroup,
      (intersectionSylow : Subgroup subgroup).map subgroup.subtype =
        ((sylow : Subgroup overgroup).map overgroup.subtype ⊓ subgroup) := by
  have : Fact subgroupPrime.Prime := ⟨hsubgroupPrime⟩
  let sylowImage := (sylow : Subgroup overgroup).map overgroup.subtype
  let intersection := sylowImage ⊓ subgroup
  have hintersectionNormalized : actor ≤ Subgroup.normalizer (intersection : Set G) :=
    normalizes_inf_of_normalizes_both actor sylowImage subgroup hsylowNormalized hsubgroupNormalized
  have hintersectionGroup : IsPGroup subgroupPrime intersection :=
    (sylow.isPGroup'.map overgroup.subtype).to_le inf_le_left
  have hsubgroupComplement : ¬prime ∣ Nat.card subgroup := fun hdiv =>
    hcomplement (hdiv.trans (Subgroup.card_dvd_of_le hle))
  obtain ⟨firstSylow, hintersectionLe, hfirstNormalized⟩ :=
    exists_normalized_sylow_containing_normalized_pSubgroup prime hprime subgroupPrime hsubgroupPrime
      actor subgroup intersection hpgroup hsubgroupComplement hsubgroupNormalized inf_le_right
        hintersectionGroup hintersectionNormalized
  let firstImage := (firstSylow : Subgroup subgroup).map subgroup.subtype
  obtain ⟨secondSylow, hfirstSecondLe, hsecondNormalized⟩ :=
    exists_normalized_sylow_containing_normalized_pSubgroup prime hprime subgroupPrime hsubgroupPrime
      actor overgroup firstImage hpgroup hcomplement hovergroupNormalized
        ((Subgroup.map_subtype_le _).trans hle) (firstSylow.isPGroup'.map subgroup.subtype) hfirstNormalized
  let secondImage := (secondSylow : Subgroup overgroup).map overgroup.subtype
  have hsecondIntersection : secondImage ⊓ subgroup = firstImage := by
    have hinternalGroup : IsPGroup subgroupPrime ((secondImage ⊓ subgroup).subgroupOf subgroup) :=
      ((secondSylow.isPGroup'.map overgroup.subtype).to_le inf_le_left).comap_subtype
    have hfirstInternal : (firstSylow : Subgroup subgroup) ≤ (secondImage ⊓ subgroup).subgroupOf subgroup := by
      intro member hmember
      exact ⟨hfirstSecondLe (Subgroup.mem_map_of_mem subgroup.subtype hmember), member.property⟩
    have heq := firstSylow.is_maximal' hinternalGroup hfirstInternal
    have hmapped := congrArg (fun subgroup' : Subgroup subgroup => subgroup'.map subgroup.subtype) heq
    rw [Subgroup.map_subgroupOf_eq_of_le (show secondImage ⊓ subgroup ≤ subgroup from inf_le_right)] at hmapped
    exact hmapped
  obtain ⟨conjugator, hconjugator, hconjugacy⟩ := exists_centralizing_conjugator_of_normalized_sylows
    prime hprime subgroupPrime hsubgroupPrime actor overgroup hpgroup hcomplement hovergroupNormalized
      secondSylow sylow hsecondNormalized hsylowNormalized
  have hsubgroupConjugate : subgroup.map (MulAut.conj conjugator).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hfixedNormalized hconjugator)
  have hfirstConjugate : firstImage.map (MulAut.conj conjugator).toMonoidHom = intersection := by
    rw [← hsecondIntersection, Subgroup.map_inf _ _ _ (MulAut.conj conjugator).injective,
      hconjugacy, hsubgroupConjugate]
  have hcard : Nat.card intersection = Nat.card (firstSylow : Subgroup subgroup) := by
    rw [← hfirstConjugate, Subgroup.card_map_of_injective (MulAut.conj conjugator).injective,
      Subgroup.card_map_of_injective subgroup.subtype_injective]
  have hfirstLe : firstImage ≤ intersection := by
    have hcardLe : Nat.card firstImage ≤ Nat.card intersection := by
      rw [Subgroup.card_map_of_injective subgroup.subtype_injective, hcard]
    have heq : intersection = firstImage :=
      Subgroup.eq_of_le_of_card_ge hintersectionLe hcardLe
    exact heq.symm ▸ le_rfl
  refine ⟨firstSylow, le_antisymm hfirstLe hintersectionLe⟩

end CFSG.RankThreeEvenClassification.Helpers
