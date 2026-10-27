module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersectionSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem pairFlipGroup_eq_generated (H : Subgroup G)
    (beta : rightCosetSpace H) (t : G) :
    pairFlipGroup H beta t =
      Subgroup.closure ((pairPointStabilizer H beta : Set G) ∪ {t}) := by
  rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure]
  rfl

theorem pairFlipGroup_le_normalizer_iff (H : Subgroup G)
    (beta : rightCosetSpace H) (t : G) (X : Subgroup G) :
    pairFlipGroup H beta t ≤ Subgroup.normalizer (X : Set G) ↔
      pairPointStabilizer H beta ≤ Subgroup.normalizer (X : Set G) ∧
        t ∈ Subgroup.normalizer (X : Set G) := by
  rw [pairFlipGroup, sup_le_iff, Subgroup.zpowers_le]

theorem pair_class_mem_generated {H : Subgroup G}
    {beta : rightCosetSpace H} {t s : G}
    (hs : s ∈ conjugacyWithin (pairPointStabilizer H beta) t) :
    s ∈ pairFlipGroup H beta t := by
  obtain ⟨b, rfl⟩ := hs
  exact (pairFlipGroup H beta t).mul_mem
    ((pairFlipGroup H beta t).mul_mem
      ((pairFlipGroup H beta t).inv_mem
        (pairPointStabilizer_le_pairFlipGroup H beta t b.property))
      (flip_mem_pairFlipGroup H beta t))
    (pairPointStabilizer_le_pairFlipGroup H beta t b.property)

theorem right_conjugate_mem_normalizer {A : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (A : Set G)) (e : G) :
    rightConjugateElem s e ∈ Subgroup.normalizer (rightConjugate A e : Set G) := by
  have h := Subgroup.le_normalizer_map
    (H := A) (MulAut.conj e⁻¹).toMonoidHom
    (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
  simpa only [rightConjugate, Subgroup.conjBy, rightConjugateElem,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h

theorem sylow_ambient_right_conjugate [Finite G]
    (E : Subgroup G) (p : ℕ) (hp : p.Prime) (P₀ P : Sylow p E) :
    ∃ e : E, rightConjugate ((P₀ : Subgroup E).map E.subtype) (e : G) =
      (P : Subgroup E).map E.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq E P₀ P
  refine ⟨e⁻¹, ?_⟩
  have hcoeff : (P₀ : Subgroup E).map (MulAut.conj e).toMonoidHom =
      (P : Subgroup E) := by
    rw [← he, Sylow.coe_subgroup_smul]
    rfl
  have hcomp : (MulAut.conj (e : G)).toMonoidHom.comp E.subtype =
      E.subtype.comp (MulAut.conj e).toMonoidHom := by
    ext x
    rfl
  change ((P₀ : Subgroup E).map E.subtype).map
    (MulAut.conj ((e⁻¹ : E) : G)⁻¹).toMonoidHom = _
  simp only [Subgroup.coe_inv, inv_inv]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hcoeff]

theorem normalized_intersection_sylow_corrector [Finite G]
    (H : Subgroup G) (beta : rightCosetSpace H) (t : G)
    (E X : Subgroup G) (hEB : E ≤ pairPointStabilizer H beta)
    (hX : pairFlipGroup H beta t ≤ Subgroup.normalizer (X : Set G))
    (p : ℕ) (hp : p.Prime) (P₀ : Sylow p E) (s₀ : G)
    (hs₀ : s₀ ∈ conjugacyWithin (pairPointStabilizer H beta) t)
    (hs₀norm : s₀ ∈ Subgroup.normalizer
      (((P₀ : Subgroup E).map E.subtype : Subgroup G) : Set G))
    (Q : Sylow p (X ⊓ E : Subgroup G)) :
    (conjugacyWithin (pairPointStabilizer H beta) t ∩
      (Subgroup.normalizer
        (((Q : Subgroup (X ⊓ E : Subgroup G)).map (X ⊓ E).subtype : Subgroup G) :
          Set G) : Set G)).Nonempty := by
  obtain ⟨P, hPQ⟩ := sylow_intersection_extension X E Q
  obtain ⟨e, he⟩ := sylow_ambient_right_conjugate E p hp P₀ P
  let s : G := rightConjugateElem s₀ (e : G)
  have hsclass : s ∈ conjugacyWithin (pairPointStabilizer H beta) t := by
    obtain ⟨b, hb⟩ := hs₀
    refine ⟨b * (⟨(e : G), hEB e.property⟩ : pairPointStabilizer H beta), ?_⟩
    simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, s, rightConjugateElem]
    rw [← hb]
    simp only [mul_assoc]
  have hsP : s ∈ Subgroup.normalizer
      (((P : Subgroup E).map E.subtype : Subgroup G) : Set G) := by
    rw [← he]
    exact right_conjugate_mem_normalizer hs₀norm (e : G)
  have hsX : s ∈ Subgroup.normalizer (X : Set G) :=
    hX (pair_class_mem_generated hsclass)
  refine ⟨s, hsclass, ?_⟩
  rw [← hPQ]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hsP, hsX⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection
