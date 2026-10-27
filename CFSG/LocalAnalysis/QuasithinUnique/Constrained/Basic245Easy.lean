module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem ConstrainedSetting.isSylowTwoOf_normalizer (hcs : ConstrainedSetting G T M H S L)
    {S₀ : Subgroup G} (hS₀ : S₀ ≠ ⊥) (hS₀S : S₀ ≤ S)
    (hHN : H ≤ Subgroup.normalizer (S₀ : Set G)) :
    IsSylowTwoOf S (Subgroup.normalizer (S₀ : Set G)) := by
  have hS₀2 : IsPGroup 2 S₀ := hcs.sylow.isPGroup.to_le hS₀S
  have hΓ : IsGamma M (Subgroup.normalizer (S₀ : Set G)) := by
    refine ⟨fun hbot => hS₀ ?_, ?_⟩
    · have : S₀ ≤ pCoreOf 2 (Subgroup.normalizer (S₀ : Set G)) :=
        le_pCoreOf_of_normalizes Subgroup.le_normalizer le_rfl hS₀2
      rw [hbot] at this
      exact le_bot_iff.mp this
    · obtain ⟨-, U, HU, hp, hle⟩ := hcs.gamma0.isGamma
      exact ⟨U, HU, hp, hle.trans hHN⟩
  exact (hcs.gamma0.overgroup_of_le hcs.setting hcs.sylow_inf hΓ hHN).2.1

theorem lemma244 : Lemma244 := by
  intro G _ _ T M H S L hcs S₀ hS₀ hS₀S hHN
  have hSyl := hcs.isSylowTwoOf_normalizer hS₀ hS₀S hHN
  exact hSyl.eq_of_le (le_inf hcs.le_T hSyl.le) inf_le_right
    (hcs.setting.isPGroup.to_le inf_le_left)

end CFSG.QuasithinUnique
