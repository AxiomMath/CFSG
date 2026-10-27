module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingSymmetry

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

theorem theorem_2_part_one {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (g : G)
    (hg : g ∉ Subgroup.normalizer (Q : Set G))
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))
    (S : Sylow 2 ↥(Q ⊔ sylowImage _ T))
    (hTS : sylowImage _ T ≤ sylowImage _ S) (hne : sylowImage _ T ≠ ⊥) :
    let A := sylowImage (rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)) T
    let X := sylowImage (Q ⊔ A) S
    let N := relativeNormalizer A X
    N = A ⊔ (N ⊓ Q) ∧ A ⊓ Q = ⊥ ∧
      (∀ a ∈ A, ∀ c ∈ N ⊓ Q, a * c = c * a) ∧
      ∃ (multiplication : A × ↥(N ⊓ Q) ≃* N) (factor : A ≃* ↥(N ⊓ Q))
          (square : A × A ≃* N),
        (∀ pair, (multiplication pair).val = pair.1.val * pair.2.val) ∧
        (∀ pair, (square pair).val = pair.1.val * (factor pair.2).val) := by
  dsimp only
  let A : Subgroup G := sylowImage
    (rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)) T
  let X : Subgroup G := sylowImage (Q ⊔ A) S
  let N : Subgroup G := relativeNormalizer A X
  have hdisjoint : Disjoint A Q :=
    disjoint_iff.mpr (overlap_sylow_inf_eq_bot Q htight g hg T)
  have hnormalizes : A ≤ Subgroup.normalizer (Q : Set G) := overlap_sylow_le_normalizer Q g T
  obtain ⟨factor⟩ := overlap_normalizer_factor_equiv Q htight g hg T S hTS hne
  let multiplication : A × ↥(N ⊓ Q) ≃* N :=
    relativeNormalizerProductEquiv Q A X hnormalizes hdisjoint hTS (sylowImage_le _ S)
  let square : A × A ≃* N := ((MulEquiv.refl A).prodCongr factor).trans multiplication
  refine ⟨overlap_relativeNormalizer_product Q g T S hTS,
    overlap_sylow_inf_eq_bot Q htight g hg T,
    relativeNormalizer_factors_commute Q A X hnormalizes hdisjoint,
    multiplication, factor, square, ?_, ?_⟩
  · exact relativeNormalizerProductEquiv_apply Q A X hnormalizes hdisjoint hTS (sylowImage_le _ S)
  · intro pair
    exact relativeNormalizerProductEquiv_apply Q A X hnormalizes hdisjoint hTS
      (sylowImage_le _ S) (pair.1, factor pair.2)

theorem actual_relativeNormalizer_eq {G : Type*} [Group G]
    (A X : Subgroup G) (hAX : A ≤ X) :
    (Subgroup.normalizer ((A.subgroupOf X : Subgroup X) : Set X)).map X.subtype =
      relativeNormalizer A X := by
  rw [← Subgroup.subgroupOf_normalizer_eq hAX, Subgroup.subgroupOf_map_subtype]
  rfl

theorem theorem_2_part_one_actual_normalizer {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (g : G)
    (hg : g ∉ Subgroup.normalizer (Q : Set G))
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))
    (S : Sylow 2 ↥(Q ⊔ sylowImage _ T))
    (hTS : sylowImage _ T ≤ sylowImage _ S) (hne : sylowImage _ T ≠ ⊥) :
    let A := sylowImage (rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)) T
    let X := sylowImage (Q ⊔ A) S
    let N := Subgroup.normalizer ((A.subgroupOf X : Subgroup X) : Set X)
    N.map X.subtype = A ⊔ (N.map X.subtype ⊓ Q) ∧ A ⊓ Q = ⊥ ∧
      Nonempty (N ≃* A × A) := by
  dsimp only
  let A : Subgroup G := sylowImage
    (rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)) T
  let X : Subgroup G := sylowImage (Q ⊔ A) S
  let N := Subgroup.normalizer ((A.subgroupOf X : Subgroup X) : Set X)
  have hmap : N.map X.subtype = relativeNormalizer A X := actual_relativeNormalizer_eq A X hTS
  obtain ⟨hproduct, hbot, _, multiplication, factor, square, _, _⟩ :=
    theorem_2_part_one Q htight g hg T S hTS hne
  refine ⟨?_, hbot, ?_⟩
  · rw [hmap]
    exact hproduct
  · exact ⟨((N.equivMapOfInjective X.subtype X.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)).trans square.symm⟩

end CFSG.ComponentClassification.AschbacherTightEmbedding
