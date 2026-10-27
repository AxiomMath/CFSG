module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingSylow

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

variable {G G' : Type*} [Group G] [Group G']

theorem overlapClosure_map (e : G ≃* G') (A₁ A₂ : Subgroup G) :
    overlapClosure (A₁.map e.toMonoidHom) (A₂.map e.toMonoidHom) =
      (overlapClosure A₁ A₂).map e.toMonoidHom := by
  have key : ∀ (X Y : Subgroup G) (g : G),
      rightConjugate (X.map e.toMonoidHom) (e g) ⊓ Y.map e.toMonoidHom ≠ ⊥ ↔
        rightConjugate X g ⊓ Y ≠ ⊥ := by
    intro X Y g
    rw [rightConjugate_map_equiv, MulEquiv.symm_apply_apply,
      ← Subgroup.map_inf _ _ _ e.injective]
    exact not_congr (Subgroup.map_eq_bot_iff_of_injective _ e.injective)
  unfold overlapClosure
  rw [MonoidHom.map_closure]
  congr 1
  ext g'
  constructor
  · rintro ⟨X', hX', Y', hY', hg'⟩
    refine ⟨e.symm g', ?_, e.apply_symm_apply g'⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX' hY'
    have hg'' : rightConjugate X' (e (e.symm g')) ⊓ Y' ≠ ⊥ := by
      rwa [e.apply_symm_apply]
    rcases hX' with rfl | rfl <;> rcases hY' with rfl | rfl
    · exact ⟨A₁, by simp, A₁, by simp, (key A₁ A₁ _).mp hg''⟩
    · exact ⟨A₁, by simp, A₂, by simp, (key A₁ A₂ _).mp hg''⟩
    · exact ⟨A₂, by simp, A₁, by simp, (key A₂ A₁ _).mp hg''⟩
    · exact ⟨A₂, by simp, A₂, by simp, (key A₂ A₂ _).mp hg''⟩
  · rintro ⟨g, ⟨X, hX, Y, hY, hg⟩, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
    refine ⟨X.map e.toMonoidHom, ?_, Y.map e.toMonoidHom, ?_, (key X Y g).mpr hg⟩
    · rcases hX with rfl | rfl <;> simp
    · rcases hY with rfl | rfl <;> simp

theorem relStronglyClosed_map (e : G ≃* G') {Y S : Subgroup G} {A : Set G}
    (h : relStronglyClosed Y A S) :
    relStronglyClosed (Y.map e.toMonoidHom) (e '' A) (S.map e.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨y, hy, rfl⟩ hmem
  have hmem' : y⁻¹ * a * y ∈ S := by
    obtain ⟨w, hw, hwe⟩ := hmem
    have : w = y⁻¹ * a * y := e.injective (by rw [map_mul, map_mul, map_inv]; exact hwe)
    rw [← this]
    exact hw
  exact ⟨y⁻¹ * a * y, h a ha y hy hmem', by simp⟩

theorem image_union_map (e : G ≃* G') (A₁ A₂ : Subgroup G) :
    (e '' ((A₁ : Set G) ∪ A₂)) = ((A₁.map e.toMonoidHom : Subgroup G') : Set G') ∪
      (A₂.map e.toMonoidHom : Subgroup G') := by
  rw [Set.image_union, Subgroup.coe_map, Subgroup.coe_map]
  rfl

theorem pRank_map_mulEquiv [Finite G] [Finite G'] (e : G ≃* G') (A : Subgroup G) :
    pRank 2 (A.map e.toMonoidHom) = pRank 2 A := by
  apply le_antisymm
  · have h := CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) e.symm.toMonoidHom
      e.symm.injective (A.map e.toMonoidHom)
    rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G by
      ext; simp, Subgroup.map_id] at h
  · exact CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) e.toMonoidHom e.injective A

theorem Hyp.map_mulEquiv [Finite G] [Finite G'] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}
    (h : Hyp S A₁ A₂) (e : G ≃* G') :
    Hyp (S.mapSurjective (show Function.Surjective e.toMonoidHom from e.surjective))
      (A₁.map e.toMonoidHom) (A₂.map e.toMonoidHom) where
  le_one := Subgroup.map_mono h.le_one
  le_two := Subgroup.map_mono h.le_two
  comm := by rw [← Subgroup.map_commutator, h.comm, Subgroup.map_bot]
  rank_one := by rw [pRank_map_mulEquiv]; exact h.rank_one
  rank_two := by rw [pRank_map_mulEquiv]; exact h.rank_two
  closed_overlap := by
    show relStronglyClosed _ _ (_ ⊓ (S : Subgroup G).map e.toMonoidHom)
    rw [overlapClosure_map, ← image_union_map, ← Subgroup.map_inf _ _ _ e.injective]
    exact relStronglyClosed_map e h.closed_overlap
  closed_one := by
    show relStronglyClosed _ _ ((S : Subgroup G).map e.toMonoidHom ⊓ _)
    rw [← image_union_map, ← Subgroup.map_equiv_normalizer_eq,
      ← Subgroup.map_inf _ _ _ e.injective, ← Subgroup.map_top_of_surjective e.toMonoidHom
        e.surjective]
    exact relStronglyClosed_map e h.closed_one
  closed_two := by
    show relStronglyClosed _ _ ((S : Subgroup G).map e.toMonoidHom ⊓ _)
    rw [← image_union_map, ← Subgroup.map_equiv_normalizer_eq,
      ← Subgroup.map_inf _ _ _ e.injective, ← Subgroup.map_top_of_surjective e.toMonoidHom
        e.surjective]
    exact relStronglyClosed_map e h.closed_two

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
