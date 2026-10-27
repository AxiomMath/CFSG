module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ReplacementProduct

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem right_conjugate_eq_mul_source_commutator {G : Type u} [Group G] (member element : G) :
    element⁻¹ * member * element = member * (member⁻¹ * element⁻¹ * member * element) := by group

theorem source_commutator_mem_derived {G : Type u} [Group G]
    (subgroup : Subgroup G) (first second : G) (hfirst : first ∈ subgroup) (hsecond : second ∈ subgroup) :
    first⁻¹ * second⁻¹ * first * second ∈ ⁅subgroup, subgroup⁆ := by
  have hmem := Subgroup.commutator_mem_commutator (subgroup.inv_mem hfirst) (subgroup.inv_mem hsecond)
  simpa only [commutatorElement_def, inv_inv] using hmem

theorem ReplacementDatum.join_normalized {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementNormalizer normal abelian ≤ Subgroup.normalizer (replacementJoin abelian element : Set G) :=
  (le_inf (replacementNormalizer_le_normalizer normal abelian) datum.conjugate_normalized).trans
    (Subgroup.inf_normalizer_le_normalizer_sup abelian (replacementConjugate abelian element))

theorem ReplacementDatum.intersection_normalized {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementNormalizer normal abelian ≤ Subgroup.normalizer (replacementIntersection abelian element : Set G) :=
  normalizes_inf_of_normalizes_both (replacementNormalizer normal abelian) abelian
    (replacementConjugate abelian element) (replacementNormalizer_le_normalizer normal abelian) datum.conjugate_normalized

theorem ReplacementDatum.subgroup_le_normalizer {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementSubgroup abelian element ≤ replacementNormalizer normal abelian :=
  (sup_le (inf_le_left.trans le_sup_left) (replacementCommutators_le_join abelian element)).trans datum.join_le_normalizer

theorem ReplacementDatum.subgroup_normalized {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementNormalizer normal abelian ≤ Subgroup.normalizer (replacementSubgroup abelian element : Set G) := by
  have : normal.Normal := datum.normal_normal
  rw [datum.subgroup_eq_intersection_sup_normal_inf_join]
  exact (le_inf datum.intersection_normalized
    (normalizes_inf_of_normalizes_both (replacementNormalizer normal abelian)
      (replacementJoin abelian element) normal datum.join_normalized
      (by rw [Subgroup.normalizer_eq_top]; exact le_top))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem ReplacementDatum.derived_le_intersection {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) : ⁅normal, normal⁆ ≤ replacementIntersection abelian element :=
  (le_inf datum.derived_le_abelian (Subgroup.commutator_le_self normal)).trans
    datum.abelian_inf_normal_le_intersection

theorem ReplacementDatum.element_normalizes_subgroup {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    element ∈ Subgroup.normalizer (replacementSubgroup abelian element : Set G) := by
  have hintersectionMap : (replacementIntersection abelian element).map
      (MulAut.conj element⁻¹).toMonoidHom ≤ replacementSubgroup abelian element := by
    rintro value ⟨member, hmember, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [right_conjugate_eq_mul_source_commutator]
    exact (replacementSubgroup abelian element).mul_mem
      ((le_sup_left : replacementIntersection abelian element ≤ replacementSubgroup abelian element) hmember)
      ((le_sup_right : replacementCommutators abelian element ≤ replacementSubgroup abelian element)
        (Subgroup.subset_closure ⟨member, hmember.1, rfl⟩))
  have hcommutatorsMap : (replacementCommutators abelian element).map
      (MulAut.conj element⁻¹).toMonoidHom ≤ replacementSubgroup abelian element := by
    rintro value ⟨member, hmember, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [right_conjugate_eq_mul_source_commutator]
    exact (replacementSubgroup abelian element).mul_mem
      ((le_sup_right : replacementCommutators abelian element ≤ replacementSubgroup abelian element) hmember)
      ((le_sup_left : replacementIntersection abelian element ≤ replacementSubgroup abelian element)
        (datum.derived_le_intersection (source_commutator_mem_derived normal member element
          (replacementCommutators_le_normal normal abelian datum.normal_normal element datum.element_mem hmember)
            datum.element_mem)))
  have hmap : (replacementSubgroup abelian element).map
      (MulAut.conj element⁻¹).toMonoidHom ≤ replacementSubgroup abelian element := by
    rw [replacementSubgroup, Subgroup.map_sup]
    exact sup_le hintersectionMap hcommutatorsMap
  have hinverse : element⁻¹ ∈ Subgroup.normalizer (replacementSubgroup abelian element : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro member hmember
    have hmem := hmap (Subgroup.mem_map_of_mem (MulAut.conj element⁻¹).toMonoidHom hmember)
    change element⁻¹ * member * (element⁻¹)⁻¹ ∈ replacementSubgroup abelian element
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  simpa only [inv_inv] using (Subgroup.normalizer (replacementSubgroup abelian element : Set G)).inv_mem hinverse

theorem ReplacementDatum.subgroup_not_contains_normal {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) : ¬normal ≤ replacementSubgroup abelian element := by
  intro hcontains
  have hnormalLe := hcontains.trans datum.subgroup_le_normalizer
  have hinf := replacementNormalizer_inf_normal normal abelian
  rw [inf_eq_right.mpr hnormalLe] at hinf
  exact datum.normalizer_proper.ne hinf.symm

theorem ReplacementDatum.normalizer_growth {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    normal ⊓ Subgroup.normalizer (abelian : Set G) <
      normal ⊓ Subgroup.normalizer (replacementSubgroup abelian element : Set G) := by
  have hle : normal ⊓ Subgroup.normalizer (abelian : Set G) ≤
      normal ⊓ Subgroup.normalizer (replacementSubgroup abelian element : Set G) :=
    le_inf inf_le_left ((le_sup_right : normal ⊓ Subgroup.normalizer (abelian : Set G) ≤
      replacementNormalizer normal abelian).trans datum.subgroup_normalized)
  apply lt_of_le_of_ne hle
  intro heq
  have helement : element ∈ normal ⊓ Subgroup.normalizer (abelian : Set G) :=
    heq ▸ (show element ∈ normal ⊓ Subgroup.normalizer (replacementSubgroup abelian element : Set G) from
      ⟨datum.element_mem, datum.element_normalizes_subgroup⟩)
  exact datum.element_not_mem_normalizer
    ((le_sup_right : normal ⊓ Subgroup.normalizer (abelian : Set G) ≤ replacementNormalizer normal abelian) helement)

end CFSG.RankThreeEvenClassification.Helpers
