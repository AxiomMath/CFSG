module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullAutomorphisms
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoLocalHull
import CFSG.FeitThompson.OddOrderTheorem

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

open CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G]

@[expose] def hullConjugationHom (L E : Subgroup G)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) : E →* MulAut L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion hEL)

theorem hullConjugationHom_apply (L E : Subgroup G)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (e : E) (l : L) :
    (hullConjugationHom L E hEL e l : G) = e * l * (e : G)⁻¹ := rfl

theorem hullConjugationHom_ker (L E : Subgroup G)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) :
    (hullConjugationHom L E hEL).ker =
      (Subgroup.centralizer (L : Set G)).subgroupOf E := by
  ext e
  change L.normalizerMonoidHom ⟨e, hEL e.property⟩ = 1 ↔ _
  change (⟨e, hEL e.property⟩ : Subgroup.normalizer (L : Set G)) ∈
    L.normalizerMonoidHom.ker ↔ _
  rw [Subgroup.normalizerMonoidHom_ker]
  rfl

theorem hullConjugationHom_of_mem (L E : Subgroup G)
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (l : L) (hlE : (l : G) ∈ E) :
    hullConjugationHom L E hEL ⟨l, hlE⟩ = MulAut.conj l := by
  ext x
  rfl

theorem inner_representative_mem_domain
    (u : G) (L E : Subgroup G)
    (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hEC : E ≤ Subgroup.centralizer ({u} : Set G))
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hJ0 : Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer ({u} : Set G) ≤ E)
    (e : E) (l : L) (he : hullConjugationHom L E hEL e = MulAut.conj l) :
    (l : G) ∈ E := by
  let en : Subgroup.normalizer (L : Set G) := ⟨e, hEL e.property⟩
  let ln : Subgroup.normalizer (L : Set G) := ⟨l, Subgroup.le_normalizer l.property⟩
  have hen : L.normalizerMonoidHom en = MulAut.conj l := he
  have hln : L.normalizerMonoidHom ln = MulAut.conj l := by
    ext x
    rfl
  have hdker : en * ln⁻¹ ∈ L.normalizerMonoidHom.ker := by
    change L.normalizerMonoidHom (en * ln⁻¹) = 1
    rw [map_mul, map_inv, hen, hln, mul_inv_cancel]
  rw [Subgroup.normalizerMonoidHom_ker] at hdker
  have hdJ : (e : G) * (l : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := hdker
  have hdC : (e : G) * (l : G)⁻¹ ∈ Subgroup.centralizer ({u} : Set G) :=
    (Subgroup.centralizer ({u} : Set G)).mul_mem
      (hEC e.property) ((Subgroup.centralizer ({u} : Set G)).inv_mem (hLC l.property))
  have hdE := hJ0 ⟨hdJ, hdC⟩
  have hmem := E.mul_mem (E.inv_mem hdE) e.property
  have heq : ((e : G) * (l : G)⁻¹)⁻¹ * e = l := by group
  rwa [heq] at hmem

theorem hull_inner_intersection_eq_range
    (u : G) (L E : Subgroup G)
    (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hEC : E ≤ Subgroup.centralizer ({u} : Set G))
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hJ0 : Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer ({u} : Set G) ≤ E) :
    (innerAutomorphismSubgroup L).subgroupOf (hullConjugationHom L E hEL).range =
      ((hullConjugationHom L E hEL).rangeRestrict.comp (L.subgroupOf E).subtype).range := by
  ext a
  constructor
  · intro ha
    obtain ⟨e, he⟩ := a.property
    obtain ⟨l, hl⟩ := ha
    have hel : hullConjugationHom L E hEL e = MulAut.conj l := he.trans hl.symm
    have hlE := inner_representative_mem_domain u L E hEL hEC hLC hJ0 e l hel
    refine ⟨⟨⟨l, hlE⟩, l.property⟩, ?_⟩
    apply Subtype.ext
    exact (hullConjugationHom_of_mem L E hEL l hlE).trans hl
  · rintro ⟨q, rfl⟩
    let l : L := ⟨q.val.val, q.property⟩
    refine ⟨l, ?_⟩
    exact (hullConjugationHom_of_mem L E hEL l q.val.property).symm

variable [Finite G]

theorem hull_domain_intersection_odd
    (z : G) (L E N : Subgroup G) (hEN : E ≤ N)
    (hclassfree : involutionPointClass z ∩ (N : Set G) = ∅)
    (hLclass : ∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z) :
    Odd (Nat.card (L.subgroupOf E)) := by
  apply CFSG.ProperTwoGeneratedCore.odd_card_of_no_order_two
  intro e he horder
  have heorder : orderOf (e : G) = 2 := (Subgroup.orderOf_coe e).trans horder
  have hempty : (e : G) ∈ (∅ : Set G) :=
    hclassfree ▸ ⟨hLclass e he heorder, hEN e.property⟩
  exact hempty

theorem hull_conjugation_image_isSolvable
    (z u : G) (L E N : Subgroup G)
    (hEN : E ≤ N) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hEC : E ≤ Subgroup.centralizer ({u} : Set G))
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (hJ0 : Subgroup.centralizer (L : Set G) ⊓
      Subgroup.centralizer ({u} : Set G) ≤ E)
    (hclassfree : involutionPointClass z ∩ (N : Set G) = ∅)
    (hLclass : ∀ l ∈ L, orderOf l = 2 → l ∈ involutionPointClass z)
    [Group.IsSolvable (outerAutomorphismGroup L)] :
    Group.IsSolvable (hullConjugationHom L E hEL).range := by
  let : Group.IsSolvable (L.subgroupOf E) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hull_domain_intersection_odd z L E N hEN hclassfree hLclass)
  let f := (hullConjugationHom L E hEL).rangeRestrict.comp (L.subgroupOf E).subtype
  have hf : Group.IsSolvable f.range :=
    Group.isSolvable_of_surjective f.rangeRestrict_surjective
  let : Group.IsSolvable ((innerAutomorphismSubgroup L).subgroupOf
      (hullConjugationHom L E hEL).range) := by
    rw [hull_inner_intersection_eq_range u L E hEL hEC hLC hJ0]
    exact hf
  exact automorphism_subgroup_isSolvable L _

end CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
