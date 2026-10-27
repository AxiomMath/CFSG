module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ReplacementAbelian
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ReplacementGrowth
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeNormalizerStep

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem replacement_datum_exists {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) (hpgroup : IsPGroup prime G)
    (normal abelian : Subgroup G) (hnormal : normal.Normal)
    (hclass : ⁅normal, normal⁆ ≤ Subgroup.centralizer (normal : Set G))
    (hderived : ⁅normal, normal⁆ ≤ thompsonOrderCenter G)
    (hmaximum : MaximumOrderAbelian abelian) (hnotContains : ¬normal ≤ abelian)
    (hproper : normal ⊓ Subgroup.normalizer (abelian : Set G) < normal) :
    ∃ element : G, ReplacementDatum prime normal abelian element := by
  have : normal.Normal := hnormal
  have hnormalizes : abelian ≤ Subgroup.normalizer (normal : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hnormalizerProper : replacementNormalizer normal abelian < abelian ⊔ normal := by
    apply lt_of_le_of_ne (replacementNormalizer_le_sup normal abelian)
    intro heq
    have hinf := replacementNormalizer_inf_normal normal abelian
    rw [heq, inf_eq_right.mpr le_sup_right] at hinf
    exact hproper.ne hinf.symm
  obtain ⟨representative, hrepresentative, hnormalizesRepresentative, hnotRepresentative, hstepNormal, hstepIndex⟩ :=
    pGroup_exists_prime_normalizer_step_between prime hprime (abelian ⊔ normal)
      (replacementNormalizer normal abelian) (hpgroup.to_subgroup _) hnormalizerProper
  obtain ⟨element, helement, member, hmember, hproduct⟩ := normalized_sup_factorization normal abelian
    hnormalizes representative (by simpa only [sup_comm] using hrepresentative)
  have hmemberNormalizer : member ∈ replacementNormalizer normal abelian :=
    (le_sup_left : abelian ≤ replacementNormalizer normal abelian) hmember
  have hstepEq : replacementNormalizer normal abelian ⊔ Subgroup.zpowers element =
      replacementNormalizer normal abelian ⊔ Subgroup.zpowers representative := by
    apply le_antisymm
    · apply sup_le le_sup_left
      apply Subgroup.zpowers_le_of_mem
      have heq : element = representative * member⁻¹ := by rw [← hproduct]; group
      rw [heq]
      exact (replacementNormalizer normal abelian ⊔ Subgroup.zpowers representative : Subgroup G).mul_mem
        ((le_sup_right : Subgroup.zpowers representative ≤
          replacementNormalizer normal abelian ⊔ Subgroup.zpowers representative) (Subgroup.mem_zpowers _))
        ((le_sup_left : replacementNormalizer normal abelian ≤
          replacementNormalizer normal abelian ⊔ Subgroup.zpowers representative)
          ((replacementNormalizer normal abelian).inv_mem hmemberNormalizer))
    · apply sup_le le_sup_left
      apply Subgroup.zpowers_le_of_mem
      rw [← hproduct]
      exact (replacementNormalizer normal abelian ⊔ Subgroup.zpowers element : Subgroup G).mul_mem
        ((le_sup_right : Subgroup.zpowers element ≤ replacementNormalizer normal abelian ⊔ Subgroup.zpowers element)
          (Subgroup.mem_zpowers _))
        ((le_sup_left : replacementNormalizer normal abelian ≤
          replacementNormalizer normal abelian ⊔ Subgroup.zpowers element) hmemberNormalizer)
  refine ⟨element, ⟨hprime, hodd, hpgroup, hnormal, hclass, hderived, hmaximum,
    hnotContains, hproper, helement, ?_, ?_⟩⟩
  · rwa [hstepEq]
  · rwa [hstepEq]

theorem glauberman_replacement {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime) (hpgroup : IsPGroup prime G)
    (normal : Subgroup G) (hnormal : normal.Normal)
    (hclass : ⁅normal, normal⁆ ≤ Subgroup.centralizer (normal : Set G))
    (hderived : ⁅normal, normal⁆ ≤ thompsonOrderCenter G) :
    (∀ abelian : Subgroup G, MaximumOrderAbelian abelian → normal ≤ abelian) ∨
      ∃ abelian : Subgroup G, MaximumOrderAbelian abelian ∧ ¬normal ≤ abelian ∧
        normal ≤ Subgroup.normalizer (abelian : Set G) := by
  classical
  by_cases hall : ∀ abelian : Subgroup G, MaximumOrderAbelian abelian → normal ≤ abelian
  · exact Or.inl hall
  · right
    push Not at hall
    let orders := {order : ℕ | ∃ abelian : Subgroup G, MaximumOrderAbelian abelian ∧
      ¬normal ≤ abelian ∧ Nat.card (normal ⊓ Subgroup.normalizer (abelian : Set G) : Subgroup G) = order}
    have hnonempty : orders.Nonempty := by
      obtain ⟨abelian, hmaximum, hnot⟩ := hall
      exact ⟨_, abelian, hmaximum, hnot, rfl⟩
    have hbounded : BddAbove orders := by
      refine ⟨Nat.card normal, ?_⟩
      rintro order ⟨abelian, _, _, rfl⟩
      exact Subgroup.card_le_of_le inf_le_left
    obtain ⟨abelian, hmaximum, hnot, hcard⟩ := Nat.sSup_mem hnonempty hbounded
    refine ⟨abelian, hmaximum, hnot, ?_⟩
    by_contra hnotNormalized
    have hproper : normal ⊓ Subgroup.normalizer (abelian : Set G) < normal := by
      apply lt_of_le_of_ne inf_le_left
      intro heq
      exact hnotNormalized (inf_eq_left.mp heq)
    obtain ⟨element, datum⟩ := replacement_datum_exists prime hprime hodd hpgroup normal abelian hnormal
      hclass hderived hmaximum hnot hproper
    have hnewMem : Nat.card (normal ⊓ Subgroup.normalizer (replacementSubgroup abelian element : Set G) : Subgroup G) ∈ orders :=
      ⟨replacementSubgroup abelian element, datum.subgroup_maximum, datum.subgroup_not_contains_normal, rfl⟩
    have hnewLe := le_csSup hbounded hnewMem
    have hstrict := subgroup_card_lt_of_lt _ _ datum.normalizer_growth
    rw [hcard] at hstrict
    omega

end CFSG.RankThreeEvenClassification.Helpers
