module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type} [Group G]

theorem IsGomiParabolicSwap.map_conj_map_conj {S L : Subgroup G} (h : IsGomiParabolicSwap S L)
    (x : G) :
    IsGomiParabolicSwap (S.map (MulAut.conj x).toMonoidHom)
      (L.map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨s, hs, P, hP1, hP2, hsP⟩ := h
  refine ⟨(MulAut.conj x) s, ⟨mem_map_of_mem _ hs.1, ?_⟩,
    P.map (MulAut.conj x).toMonoidHom, ?_, ?_, ?_⟩
  · have hmem := mem_map_of_mem (MulAut.conj x).toMonoidHom hs.2
    rwa [map_equiv_normalizer_eq L (MulAut.conj x)] at hmem
  · rw [← map_inf S L (MulAut.conj x).toMonoidHom (MulAut.conj x).injective,
      ← map_equiv_normalizer_eq (S ⊓ L) (MulAut.conj x),
      ← map_inf L (normalizer ((S ⊓ L : Subgroup G) : Set G)) (MulAut.conj x).toMonoidHom
        (MulAut.conj x).injective]
    exact (map_lt_map_iff_of_injective (MulAut.conj x).injective).mpr hP1
  · exact (map_lt_map_iff_of_injective (MulAut.conj x).injective).mpr hP2
  · intro hmem
    rw [← map_equiv_normalizer_eq P (MulAut.conj x)] at hmem
    exact hsP ((mem_map_iff_mem (MulAut.conj x).injective).mp hmem)

theorem isGomiParabolicSwap_inf_normalizer_iff {S L : Subgroup G} :
    IsGomiParabolicSwap (S ⊓ normalizer (L : Set G)) L ↔ IsGomiParabolicSwap S L := by
  have hS' : (S ⊓ normalizer (L : Set G)) ⊓ normalizer (L : Set G) =
      S ⊓ normalizer (L : Set G) := inf_eq_left.mpr inf_le_right
  have hL' : (S ⊓ normalizer (L : Set G)) ⊓ L = S ⊓ L := by
    rw [inf_assoc, inf_eq_right.mpr L.le_normalizer]
  unfold IsGomiParabolicSwap
  rw [hS', hL']

theorem IsGomiParabolicSwap.of_subgroupOf {K S L : Subgroup G} (hSK : S ≤ K) (hLK : L ≤ K)
    (h : IsGomiParabolicSwap (S.subgroupOf K) (L.subgroupOf K)) :
    IsGomiParabolicSwap S L := by
  have h' := h.map_subtype
  rwa [Subgroup.map_subgroupOf_eq_of_le hSK, Subgroup.map_subgroupOf_eq_of_le hLK] at h'

end CFSG.GroupTheory

end
