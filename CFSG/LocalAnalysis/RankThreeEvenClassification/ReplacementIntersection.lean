module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.AbelianNormalProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ReplacementData

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem conjugated_subgroup_normalized {G : Type u} [Group G]
    (subgroup overgroup : Subgroup G) (element : G)
    (hsubgroup : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    (helement : element ∈ Subgroup.normalizer (overgroup : Set G)) :
    overgroup ≤ Subgroup.normalizer (subgroup.map (MulAut.conj element).toMonoidHom : Set G) := by
  have hmapped := Subgroup.map_mono (f := (MulAut.conj element).toMonoidHom) hsubgroup
  rw [Subgroup.map_equiv_normalizer_eq] at hmapped
  have heq : overgroup.map (MulAut.conj element).toMonoidHom = overgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp helement
  rw [heq] at hmapped
  exact hmapped

theorem ReplacementDatum.conjugate_normalized {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementNormalizer normal abelian ≤
      Subgroup.normalizer (replacementConjugate abelian element : Set G) :=
  conjugated_subgroup_normalized abelian (replacementNormalizer normal abelian) element⁻¹
    (replacementNormalizer_le_normalizer normal abelian)
    ((Subgroup.normalizer (replacementNormalizer normal abelian : Set G)).inv_mem
      datum.element_normalizes_normalizer)

theorem ReplacementDatum.conjugate_le_normalizer {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementConjugate abelian element ≤ replacementNormalizer normal abelian := by
  rintro member ⟨representative, hrepresentative, rfl⟩
  exact Subgroup.le_normalizer_iff.mp
    (Subgroup.zpowers_le_of_mem
      ((Subgroup.normalizer (replacementNormalizer normal abelian : Set G)).inv_mem
        datum.element_normalizes_normalizer)) element⁻¹ (Subgroup.mem_zpowers _)
    representative ((le_sup_left : abelian ≤ replacementNormalizer normal abelian) hrepresentative)

theorem ReplacementDatum.join_le_normalizer {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementJoin abelian element ≤ replacementNormalizer normal abelian :=
  sup_le le_sup_left datum.conjugate_le_normalizer

theorem ReplacementDatum.mutually_normalizing {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    abelian ≤ Subgroup.normalizer (replacementConjugate abelian element : Set G) ∧
      replacementConjugate abelian element ≤ Subgroup.normalizer (abelian : Set G) :=
  ⟨(le_sup_left : abelian ≤ replacementNormalizer normal abelian).trans datum.conjugate_normalized,
    datum.conjugate_le_normalizer.trans (replacementNormalizer_le_normalizer normal abelian)⟩

theorem ReplacementDatum.intersection_central {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    replacementIntersection abelian element ≤ Subgroup.centralizer (replacementJoin abelian element : Set G) :=
  abelian_inf_le_centralizer_sup abelian (replacementConjugate abelian element) datum.maximum.1
    (replacementConjugate_commutative abelian element datum.maximum.1)

theorem ReplacementDatum.join_classTwo {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    commutator (replacementJoin abelian element) ≤ Subgroup.center (replacementJoin abelian element) :=
  mutually_normalizing_abelian_sup_classTwo abelian (replacementConjugate abelian element) datum.maximum.1
    (replacementConjugate_commutative abelian element datum.maximum.1)
    datum.mutually_normalizing.1 datum.mutually_normalizing.2

theorem ReplacementDatum.derived_le_abelian {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) : ⁅normal, normal⁆ ≤ abelian := by
  apply datum.derived_thompson.trans
  rw [thompsonOrderCenter_eq_intersection]
  exact iInf_le _ (⟨abelian, datum.maximum⟩ : {candidate : Subgroup G // MaximumOrderAbelian candidate})

theorem ReplacementDatum.abelian_inf_normal_normalized {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    normal ≤ Subgroup.normalizer ((abelian ⊓ normal : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff_commutator_le_right.mpr
  apply le_inf
  · exact (Subgroup.commutator_mono le_rfl inf_le_right).trans datum.derived_le_abelian
  · exact (Subgroup.commutator_mono le_rfl inf_le_right).trans (Subgroup.commutator_le_self normal)

theorem ReplacementDatum.abelian_inf_normal_le_intersection {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    abelian ⊓ normal ≤ replacementIntersection abelian element := by
  apply le_inf inf_le_left
  intro member hmember
  have hconjugate : element * member * element⁻¹ ∈ abelian ⊓ normal :=
    Subgroup.le_normalizer_iff.mp datum.abelian_inf_normal_normalized element datum.element_mem member hmember
  refine Subgroup.mem_map.mpr ⟨element * member * element⁻¹, hconjugate.1, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group

end CFSG.RankThreeEvenClassification.Helpers
