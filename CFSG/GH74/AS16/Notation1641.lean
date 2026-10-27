module

public import CFSG.GH74.AS16.Delta

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem isSylowTwoOf_iff [Finite G] {S H : Subgroup G} :
    QuasithinUnique.IsSylowTwoOf S H ↔ IsSylowOf 2 S H := by
  rw [isSylowOf_iff]
  rfl

theorem inDelta_rightConjugate {K K' : Subgroup G} (hK' : InDelta K K') {h : G}
    (hh : h ∈ normalizer (K : Set G)) : InDelta K (rightConjugate K' h) := by
  obtain ⟨⟨g, hg⟩, hne, hev⟩ := hK'
  have hK'conj : K' = rightConjugate K g⁻¹ := by rw [hg, map_conj_eq_rightConjugate]
  refine ⟨⟨(g⁻¹ * h)⁻¹, ?_⟩, ?_, ?_⟩
  · rw [map_conj_eq_rightConjugate, inv_inv, hK'conj, rightConjugate_mul]
  · intro heq
    apply hne
    have h1 : rightConjugate (rightConjugate K' h) h⁻¹ = rightConjugate K h⁻¹ := by rw [heq]
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    rw [h1]
    exact (rightConjugate_eq_self_iff K h⁻¹).mpr (inv_mem hh)
  · have hN : rightConjugate (normalizer (K : Set G)) h = normalizer (K : Set G) :=
      (rightConjugate_eq_self_iff _ h).mpr (le_normalizer hh)
    have h2 : rightConjugate (K' ⊓ normalizer (K : Set G)) h =
        rightConjugate K' h ⊓ normalizer (K : Set G) := by rw [rightConjugate_inf, hN]
    rw [← h2, rightConjugate_card]
    exact hev

end CFSG.GH74.AS16
