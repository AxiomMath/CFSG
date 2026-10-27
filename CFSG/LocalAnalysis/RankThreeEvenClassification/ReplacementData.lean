module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSize
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonFoundations

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

@[expose] noncomputable def replacementNormalizer {G : Type u} [Group G] (normal abelian : Subgroup G) : Subgroup G :=
  abelian ⊔ (normal ⊓ Subgroup.normalizer (abelian : Set G))

@[expose] def replacementConjugate {G : Type u} [Group G] (abelian : Subgroup G) (element : G) : Subgroup G :=
  abelian.map (MulAut.conj element⁻¹).toMonoidHom

@[expose] def replacementJoin {G : Type u} [Group G] (abelian : Subgroup G) (element : G) : Subgroup G :=
  abelian ⊔ replacementConjugate abelian element

@[expose] def replacementIntersection {G : Type u} [Group G] (abelian : Subgroup G) (element : G) : Subgroup G :=
  abelian ⊓ replacementConjugate abelian element

@[expose] def replacementCommutators {G : Type u} [Group G] (abelian : Subgroup G) (element : G) : Subgroup G :=
  Subgroup.closure {value : G | ∃ member ∈ abelian, member⁻¹ * element⁻¹ * member * element = value}

@[expose] def replacementSubgroup {G : Type u} [Group G] (abelian : Subgroup G) (element : G) : Subgroup G :=
  replacementIntersection abelian element ⊔ replacementCommutators abelian element

structure ReplacementDatum {G : Type u} [Group G]
    (prime : ℕ) (normal abelian : Subgroup G) (element : G) : Prop where
  prime_prime : prime.Prime
  prime_odd : Odd prime
  p_group : IsPGroup prime G
  normal_normal : normal.Normal
  class_two : ⁅normal, normal⁆ ≤ Subgroup.centralizer (normal : Set G)
  derived_thompson : ⁅normal, normal⁆ ≤ thompsonOrderCenter G
  maximum : MaximumOrderAbelian abelian
  not_contains : ¬normal ≤ abelian
  normalizer_proper : normal ⊓ Subgroup.normalizer (abelian : Set G) < normal
  element_mem : element ∈ normal
  step_normal : ((replacementNormalizer normal abelian).subgroupOf
    (replacementNormalizer normal abelian ⊔ Subgroup.zpowers element)).Normal
  step_index : (replacementNormalizer normal abelian).relIndex
    (replacementNormalizer normal abelian ⊔ Subgroup.zpowers element) = prime

theorem replacementNormalizer_le_normalizer {G : Type u} [Group G] (normal abelian : Subgroup G) :
    replacementNormalizer normal abelian ≤ Subgroup.normalizer (abelian : Set G) :=
  sup_le Subgroup.le_normalizer inf_le_right

theorem replacementNormalizer_le_sup {G : Type u} [Group G] (normal abelian : Subgroup G) :
    replacementNormalizer normal abelian ≤ abelian ⊔ normal :=
  sup_le le_sup_left (inf_le_left.trans le_sup_right)

theorem replacementNormalizer_inf_normal {G : Type u} [Group G]
    (normal abelian : Subgroup G) :
    replacementNormalizer normal abelian ⊓ normal = normal ⊓ Subgroup.normalizer (abelian : Set G) := by
  apply le_antisymm
  · rintro element ⟨helement, hnormal⟩
    exact ⟨hnormal, replacementNormalizer_le_normalizer normal abelian helement⟩
  · intro element helement
    exact ⟨(le_sup_right : normal ⊓ Subgroup.normalizer (abelian : Set G) ≤
      abelian ⊔ (normal ⊓ Subgroup.normalizer (abelian : Set G))) helement, helement.1⟩

theorem ReplacementDatum.normalizer_lt_sup {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementNormalizer normal abelian < abelian ⊔ normal := by
  apply lt_of_le_of_ne (replacementNormalizer_le_sup normal abelian)
  intro heq
  have hinf := replacementNormalizer_inf_normal normal abelian
  rw [heq, inf_eq_right.mpr le_sup_right] at hinf
  exact datum.normalizer_proper.ne hinf.symm

theorem ReplacementDatum.element_normalizes_normalizer {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    element ∈ Subgroup.normalizer (replacementNormalizer normal abelian : Set G) := by
  have hnormal := (Subgroup.normal_subgroupOf_iff_le_normalizer
    (le_sup_left : replacementNormalizer normal abelian ≤
      replacementNormalizer normal abelian ⊔ Subgroup.zpowers element)).mp datum.step_normal
  exact hnormal ((le_sup_right : Subgroup.zpowers element ≤
    replacementNormalizer normal abelian ⊔ Subgroup.zpowers element) (Subgroup.mem_zpowers element))

theorem ReplacementDatum.element_not_mem_normalizer {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    element ∉ replacementNormalizer normal abelian := by
  intro helement
  have heq : replacementNormalizer normal abelian ⊔ Subgroup.zpowers element =
      replacementNormalizer normal abelian := sup_eq_left.mpr (Subgroup.zpowers_le_of_mem helement)
  have hindex := datum.step_index
  rw [heq, Subgroup.relIndex_self] at hindex
  exact datum.prime_prime.ne_one hindex.symm

theorem replacementConjugate_card {G : Type u} [Group G] (abelian : Subgroup G) (element : G) :
    Nat.card (replacementConjugate abelian element) = Nat.card abelian :=
  Subgroup.card_map_of_injective (MulAut.conj element⁻¹).injective

theorem replacementConjugate_commutative {G : Type u} [Group G]
    (abelian : Subgroup G) (element : G) (habelian : IsMulCommutative abelian) :
    IsMulCommutative (replacementConjugate abelian element) :=
  subgroup_map_commutative abelian (MulAut.conj element⁻¹).toMonoidHom habelian

end CFSG.RankThreeEvenClassification.Helpers
