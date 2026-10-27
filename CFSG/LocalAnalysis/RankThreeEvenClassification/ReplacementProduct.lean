module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ReplacementIntersection

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem normalized_sup_card_mul_inf {G : Type u} [Group G]
    (first second : Subgroup G) (hnormalizes : second ≤ Subgroup.normalizer (first : Set G)) :
    Nat.card (first ⊔ second : Subgroup G) * Nat.card (first ⊓ second : Subgroup G) =
      Nat.card first * Nat.card second := by
  have : (first.subgroupOf (second ⊔ first)).Normal :=
    normal_subgroupOf_of_normalizes first (second ⊔ first) (sup_le hnormalizes Subgroup.le_normalizer)
  have : (first.subgroupOf second).Normal := normal_subgroupOf_of_normalizes first second hnormalizes
  let equivalence := QuotientGroup.quotientInfEquivProdNormalizerQuotient second first hnormalizes
  have hquotient := Nat.card_congr equivalence.toEquiv
  have hfirst : Nat.card (first.subgroupOf (second ⊔ first)) = Nat.card first :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show first ≤ second ⊔ first from le_sup_right)).toEquiv
  have hintersection : Nat.card (first.subgroupOf second) = Nat.card (first ⊓ second : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype first second]
    exact (Subgroup.card_map_of_injective second.subtype_injective).symm
  have hsupCard := Subgroup.card_eq_card_quotient_mul_card_subgroup (first.subgroupOf (second ⊔ first))
  have hsecondCard := Subgroup.card_eq_card_quotient_mul_card_subgroup (first.subgroupOf second)
  rw [hfirst, ← hquotient] at hsupCard
  rw [hintersection] at hsecondCard
  rw [sup_comm first second, hsupCard, hsecondCard]
  ring

theorem replacementCommutators_le_join {G : Type u} [Group G] (abelian : Subgroup G) (element : G) :
    replacementCommutators abelian element ≤ replacementJoin abelian element := by
  apply (Subgroup.closure_le _).mpr
  rintro value ⟨member, hmember, rfl⟩
  have hconjugate : element⁻¹ * member * element ∈ replacementConjugate abelian element := by
    refine Subgroup.mem_map.mpr ⟨member, hmember, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have heq : member⁻¹ * element⁻¹ * member * element = member⁻¹ * (element⁻¹ * member * element) := by group
  rw [heq]
  exact (replacementJoin abelian element).mul_mem
    ((le_sup_left : abelian ≤ replacementJoin abelian element) (abelian.inv_mem hmember))
    ((le_sup_right : replacementConjugate abelian element ≤ replacementJoin abelian element) hconjugate)

theorem replacementCommutators_le_normal {G : Type u} [Group G]
    (normal abelian : Subgroup G) (hnormal : normal.Normal) (element : G) (helement : element ∈ normal) :
    replacementCommutators abelian element ≤ normal := by
  have : normal.Normal := hnormal
  apply (Subgroup.closure_le _).mpr
  rintro value ⟨member, _, rfl⟩
  have hconjugate := hnormal.conj_mem element⁻¹ (normal.inv_mem helement) member⁻¹
  have heq : member⁻¹ * element⁻¹ * member * element = (member⁻¹ * element⁻¹ * member) * element := by group
  rw [heq]
  exact normal.mul_mem (by simpa only [inv_inv] using hconjugate) helement

theorem replacementJoin_eq_abelian_sup_commutators {G : Type u} [Group G]
    (abelian : Subgroup G) (element : G) :
    replacementJoin abelian element = abelian ⊔ replacementCommutators abelian element := by
  apply le_antisymm
  · apply sup_le le_sup_left
    rintro value ⟨member, hmember, rfl⟩
    have hcommutator : member⁻¹ * element⁻¹ * member * element ∈ replacementCommutators abelian element :=
      Subgroup.subset_closure ⟨member, hmember, rfl⟩
    have heq : (MulAut.conj element⁻¹).toMonoidHom member =
        member * (member⁻¹ * element⁻¹ * member * element) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [heq]
    exact (abelian ⊔ replacementCommutators abelian element : Subgroup G).mul_mem
      ((le_sup_left : abelian ≤ abelian ⊔ replacementCommutators abelian element) hmember)
      ((le_sup_right : replacementCommutators abelian element ≤
        abelian ⊔ replacementCommutators abelian element) hcommutator)
  · exact sup_le le_sup_left (replacementCommutators_le_join abelian element)

theorem ReplacementDatum.join_normalizes_commutators {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementCommutators abelian element ≤ Subgroup.normalizer (abelian : Set G) :=
  (replacementCommutators_le_join abelian element).trans
    (datum.join_le_normalizer.trans (replacementNormalizer_le_normalizer normal abelian))

theorem ReplacementDatum.subgroup_eq_intersection_sup_normal_inf_join
    {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementSubgroup abelian element =
      replacementIntersection abelian element ⊔ (replacementJoin abelian element ⊓ normal) := by
  apply le_antisymm
  · apply sup_le le_sup_left
    exact (le_inf (replacementCommutators_le_join abelian element)
      (replacementCommutators_le_normal normal abelian datum.normal_normal element datum.element_mem)).trans le_sup_right
  · apply sup_le le_sup_left
    rintro value ⟨hjoin, hnormal⟩
    rw [replacementJoin_eq_abelian_sup_commutators] at hjoin
    obtain ⟨left, hleft, right, hright, heq⟩ := normalized_sup_factorization abelian
      (replacementCommutators abelian element) datum.join_normalizes_commutators value hjoin
    have hleftNormal : left ∈ normal := by
      have hrightNormal := replacementCommutators_le_normal normal abelian datum.normal_normal element datum.element_mem hright
      have hcancel : left = value * right⁻¹ := by rw [← heq]; group
      rw [hcancel]
      exact normal.mul_mem hnormal (normal.inv_mem hrightNormal)
    rw [← heq]
    exact (replacementSubgroup abelian element).mul_mem
      ((le_sup_left : replacementIntersection abelian element ≤ replacementSubgroup abelian element)
        (datum.abelian_inf_normal_le_intersection ⟨hleft, hleftNormal⟩))
      ((le_sup_right : replacementCommutators abelian element ≤ replacementSubgroup abelian element) hright)

theorem ReplacementDatum.subgroup_inf_abelian {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    abelian ⊓ replacementSubgroup abelian element = replacementIntersection abelian element := by
  have hcommutators : replacementCommutators abelian element ≤
      Subgroup.normalizer (replacementIntersection abelian element : Set G) := by
    intro member hmember
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr (fun central hcentral =>
        (Subgroup.mem_centralizer_iff.mp (datum.intersection_central hcentral) member
          (replacementCommutators_le_join abelian element hmember)).symm))
  apply le_antisymm
  · rintro value ⟨habelian, hsubgroup⟩
    obtain ⟨left, hleft, right, hright, heq⟩ := normalized_sup_factorization
      (replacementIntersection abelian element) (replacementCommutators abelian element) hcommutators value hsubgroup
    have hrightAbelian : right ∈ abelian := by
      have hcancel : right = left⁻¹ * value := by rw [← heq]; group
      rw [hcancel]
      exact abelian.mul_mem (abelian.inv_mem hleft.1) habelian
    have hrightIntersection := datum.abelian_inf_normal_le_intersection
      ⟨hrightAbelian, replacementCommutators_le_normal normal abelian datum.normal_normal element datum.element_mem hright⟩
    rw [← heq]
    exact (replacementIntersection abelian element).mul_mem hleft hrightIntersection
  · exact le_inf inf_le_left le_sup_left

theorem ReplacementDatum.abelian_sup_subgroup_eq_join {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (_datum : ReplacementDatum prime normal abelian element) :
    abelian ⊔ replacementSubgroup abelian element = replacementJoin abelian element := by
  apply le_antisymm
  · apply sup_le le_sup_left
    exact sup_le (inf_le_left.trans le_sup_left) (replacementCommutators_le_join abelian element)
  · rw [replacementJoin_eq_abelian_sup_commutators]
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)

theorem ReplacementDatum.subgroup_card_eq {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    Nat.card (replacementSubgroup abelian element) = Nat.card abelian := by
  have hsubgroupNormalizes : replacementSubgroup abelian element ≤ Subgroup.normalizer (abelian : Set G) :=
    (sup_le (inf_le_left.trans le_sup_left) (replacementCommutators_le_join abelian element)).trans
      (datum.join_le_normalizer.trans (replacementNormalizer_le_normalizer normal abelian))
  have hcard := normalized_sup_card_mul_inf abelian (replacementSubgroup abelian element) hsubgroupNormalizes
  rw [datum.abelian_sup_subgroup_eq_join, datum.subgroup_inf_abelian] at hcard
  have hconjugateCard := normalized_sup_card_mul_inf abelian
    (replacementConjugate abelian element) datum.mutually_normalizing.2
  rw [replacementConjugate_card] at hconjugateCard
  have hcancel : Nat.card abelian * Nat.card (replacementSubgroup abelian element) =
      Nat.card abelian * Nat.card abelian := hcard.symm.trans hconjugateCard
  exact mul_left_cancel₀ (Nat.card_pos.ne') hcancel

end CFSG.RankThreeEvenClassification.Helpers
