module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotient

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ShultStronglyClosedTI
open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem pointClass_eq_of_mem {z s : G} (hs : s ∈ involutionPointClass z) :
    involutionPointClass s = involutionPointClass z := by
  obtain ⟨g, rfl⟩ := hs
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨g * x, (rightConjugateElem_comp z g x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨g⁻¹ * x, ?_⟩
    simp only [rightConjugateElem]
    group

theorem local_point_datum_automorphism [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (f : G ≃* G) :
    InvolutionPointLocalEmbedding (H.map f.toMonoidHom) (f z) := by
  have hker : f.toMonoidHom.ker = ⊥ := f.toMonoidHom.ker_eq_bot f.injective
  have hodd : Odd (Nat.card f.toMonoidHom.ker) := by
    rw [hker, Nat.card_eq_fintype_card]
    simp
  have hproper : H.map f.toMonoidHom ≠ ⊤ := by
    intro htop
    apply h.proper
    have heq := Subgroup.comap_map_eq_self_of_injective
      (f := f.toMonoidHom) f.injective H
    rw [← heq, htop, Subgroup.comap_top]
  exact local_involution_point_embedding_image f.toMonoidHom f.surjective hodd h hproper

theorem local_point_datum_right_conjugate [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (g : G) :
    InvolutionPointLocalEmbedding (rightConjugate H g) (rightConjugateElem z g) := by
  simpa only [rightConjugate, Subgroup.conjBy, rightConjugateElem,
    MulAut.conj_apply, inv_inv] using local_point_datum_automorphism h (MulAut.conj g⁻¹)

theorem point_class_conjugate_fixed_rightCoset [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (g : G) :
    pointRightCosetMul H (rightCosetMk H g) (rightConjugateElem z g) =
      rightCosetMk H g := by
  have hbase : pointRightCosetMul H (rightCosetMk H 1) z = rightCosetMk H 1 :=
    (point_right_base_fixed_iff H z).mpr h.distinguished_mem
  have hf := point_right_fixed_conjugate hbase g
  change pointRightCosetMul H
    (pointRightCosetMul H (rightCosetMk H 1) g) (rightConjugateElem z g) =
      pointRightCosetMul H (rightCosetMk H 1) g at hf
  have hbaseg : pointRightCosetMul H (rightCosetMk H 1) g = rightCosetMk H g := by
    rw [pointRightCosetMul_eq_translate, rightCosetTranslate_mk, one_mul]
  rwa [hbaseg] at hf

theorem local_point_datum_at_class_fixed_point [Finite G]
    {H : Subgroup G} {z s : G} (h : InvolutionPointLocalEmbedding H z)
    (hs : s ∈ involutionPointClass z) (omega : pointRightCosetSpace H)
    (hfixed : pointRightCosetMul H omega s = omega) :
    InvolutionPointLocalEmbedding (rightCosetStabilizer H omega) s := by
  obtain ⟨g, rfl⟩ := hs
  have huniq := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨_, _, hu⟩ := huniq (rightConjugateElem z g) ⟨g, rfl⟩
  have heq : omega = rightCosetMk H g :=
    (hu omega hfixed).trans (hu _ (point_class_conjugate_fixed_rightCoset h g)).symm
  rw [heq, rightCosetStabilizer_mk]
  exact local_point_datum_right_conjugate h g

theorem conjugacyWithin_map_automorphism (A : Subgroup G) (s : G) (f : G ≃* G) :
    conjugacyWithin (A.map f.toMonoidHom) (f s) = f '' conjugacyWithin A s := by
  ext a
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hfy⟩ := x.property
    refine ⟨rightConjugateElem s y, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
    rw [← hx, ← hfy]
    simp only [rightConjugateElem, map_mul, map_inv]
    rfl
  · rintro ⟨a, ⟨x, rfl⟩, rfl⟩
    refine ⟨⟨f x, Subgroup.mem_map_of_mem f.toMonoidHom x.property⟩, ?_⟩
    simp only [map_mul, map_inv]

theorem conjugacyWithin_card_map_automorphism (A : Subgroup G) (s : G) (f : G ≃* G) :
    Nat.card (conjugacyWithin (A.map f.toMonoidHom) (f s)) =
      Nat.card (conjugacyWithin A s) := by
  rw [conjugacyWithin_map_automorphism]
  exact Nat.card_congr (Equiv.Set.image f _ f.injective).symm

theorem conjugacyWithin_card_normalizer_conjugate (M : Subgroup G) (s : G)
    (n : Subgroup.normalizer (M : Set G)) :
    Nat.card (conjugacyWithin M (rightConjugateElem s (n : G))) =
      Nat.card (conjugacyWithin M s) := by
  have hmap : M.map (MulAut.conj (n : G)⁻¹).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (M : Set G)).inv_mem n.property)
  simpa only [hmap, rightConjugateElem, MulAut.conj_apply, inv_inv] using
    conjugacyWithin_card_map_automorphism M s (MulAut.conj (n : G)⁻¹)

theorem normalizer_conjugate_no_pointFixedSet_fixed
    {H M : Subgroup G} {s : G}
    (hno : ∀ omega ∈ pointFixedSet H M, pointRightCosetMul H omega s ≠ omega)
    (n : Subgroup.normalizer (M : Set G)) :
    ∀ omega ∈ pointFixedSet H M,
      pointRightCosetMul H omega (rightConjugateElem s (n : G)) ≠ omega := by
  intro omega homega hf
  have hstable := normalizer_preserves_pointFixedSet
    ((Subgroup.normalizer (M : Set G)).inv_mem n.property) homega
  apply hno _ hstable
  have hh := point_right_fixed_conjugate hf (n : G)⁻¹
  have hreturn : rightConjugateElem (rightConjugateElem s (n : G)) (n : G)⁻¹ = s := by
    simp only [rightConjugateElem]
    group
  simpa only [hreturn] using hh

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
