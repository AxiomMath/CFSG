module

public import CFSG.Quasithin.Background.C1GNDefs
import CFSG.Quasithin.Background.C118Main
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Quasithin

variable {X : Type} [Group X]

theorem _root_.CFSG.Quasithin.IsC118Pair.subgroupOf {X₁ T T₁ T₂ : Subgroup X} (hTX : T ≤ X₁)
    (h : IsC118Pair T T₁ T₂) :
    IsC118Pair (T.subgroupOf X₁) (T₁.subgroupOf X₁) (T₂.subgroupOf X₁) := by
  obtain ⟨h1, h1Z, h1c, h2, h2B, h2c, hΩ⟩ := h
  have hT₁ : T₁ ≤ T := h1Z.trans (C1GN.omegaOneCenterOf_le_self T)
  have hT₂ : T₂ ≤ T := h2B.trans (C1GN.baum_le T)
  have hB : baum T ≤ X₁ := (C1GN.baum_le T).trans hTX
  have hbaum : baum (T.subgroupOf X₁) = (baum T).subgroupOf X₁ := by
    have h' : (baum (T.subgroupOf X₁)).map X₁.subtype = baum T := by
      rw [← baum_map_of_injective X₁.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hTX]
    rw [← h']
    exact (Subgroup.comap_map_eq_self_of_injective X₁.subtype_injective _).symm
  let eT : ↥(T.subgroupOf X₁) ≃* ↥T := Subgroup.subgroupOfEquivOfLe hTX
  let eB : ↥(baum (T.subgroupOf X₁)) ≃* ↥(baum T) :=
    (MulEquiv.subgroupCongr hbaum).trans (Subgroup.subgroupOfEquivOfLe hB)
  have hcT : ∀ A : Subgroup X, (A.subgroupOf T).comap eT.toMonoidHom =
      (A.subgroupOf X₁).subgroupOf (T.subgroupOf X₁) := fun A => rfl
  have hcB : ∀ A : Subgroup X, (A.subgroupOf (baum T)).comap eB.toMonoidHom =
      (A.subgroupOf X₁).subgroupOf (baum (T.subgroupOf X₁)) := fun A => rfl
  have hne : ∀ A : Subgroup X, A ≤ T → A ≠ ⊥ → A.subgroupOf X₁ ≠ ⊥ := fun A hA hA0 hbot =>
    hA0 ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le (hA.trans hTX))
  refine ⟨hne T₁ hT₁ h1, ?_, ?_, hne T₂ hT₂ h2, ?_, ?_, ?_⟩
  · rw [omegaOneCenterOf_subgroupOf hTX]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (h1Z (Subgroup.mem_subgroupOf.mp hx))
  · rw [← hcT T₁, Subgroup.comap_equiv_eq_map_symm']
    exact characteristic_map_equiv_pair eT.symm h1c
  · rw [hbaum]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (h2B (Subgroup.mem_subgroupOf.mp hx))
  · rw [← hcB T₂, Subgroup.comap_equiv_eq_map_symm']
    exact characteristic_map_equiv_pair eB.symm h2c
  · intro Ω _ _ H ι' hι' hH
    have hrange : (ι'.comp eB.symm.toMonoidHom).range = ι'.range := by
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨b', rfl⟩
        exact ⟨eB b', by simp⟩
    have hmap : ∀ A : Subgroup X, (A.subgroupOf (baum T)).map (ι'.comp eB.symm.toMonoidHom) =
        ((A.subgroupOf X₁).subgroupOf (baum (T.subgroupOf X₁))).map ι' := fun A => by
      rw [← hcB A, Subgroup.comap_equiv_eq_map_symm', Subgroup.map_map]
    rcases hΩ Ω H (ι'.comp eB.symm.toMonoidHom) (hι'.comp eB.symm.injective)
      (hrange ▸ hH) with h | h | h
    · exact Or.inl (by rwa [hmap T₁] at h)
    · exact Or.inr (Or.inl (by rwa [hmap T₂] at h))
    · exact Or.inr (Or.inr h)

end CFSG.LocalAnalysis.RankThreeUC.S15
