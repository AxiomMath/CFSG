module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3312R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Step3_3_15R_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D Y₁ Y₂ : Subgroup G), Hyp331 G T M L D →
    Y₁ ∈ lFamilyOf L T → Y₂ ∈ lFamilyOf L T → L ⊔ T = Y₁ ⊔ Y₂ ⊔ T →
    pCoreOf 2 (Y₁ ⊔ T ⊔ D) ≠ ⊥ → pCoreOf 2 (Y₂ ⊔ T ⊔ D) ≠ ⊥ →
    L3312.Type3312R (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁) → L3312.Type3312R (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂) →
    ∃ Y : Subgroup G, (Y = Y₁ ∨ Y = Y₂) ∧ ¬ D ≤ Subgroup.normalizer (Y : Set G) ∧
      IsPSL 2 2 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧ InducesInnerOn T Y ∧
      ∃ K ∈ cComp (Y ⊔ T ⊔ D), Y ≤ K ∧ IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
        Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G)

theorem step3_3_15R_of_F4 (h6 : Stmt3_3_6) (h14 : Stmt3_3_14_F4) (h12 : Step3_3_12R_F4) :
    Step3_3_15R_F4 := by
  intro G _ _ T M L D Y₁ Y₂ h hY₁ hY₂ hLT hO₁ hO₂ ht₁ ht₂
  have hnot : ¬ (D ≤ Subgroup.normalizer (Y₁ : Set G) ∧ D ≤ Subgroup.normalizer (Y₂ : Set G)) := by
    rintro ⟨hD₁, hD₂⟩
    obtain ⟨hML, -⟩ := h14 G T M L D h
    have hne : L ⊔ T ≠ ⊥ := fun hb => h.toSetup331.T_ne_bot (le_bot_iff.mp (hb ▸ le_sup_right))
    have hb := (h6 G T M L D h).2.1.2 (L ⊔ T) hne (by rw [hML]) (by rw [hML]; exact
      Subgroup.le_normalizer)
    apply hb
    rw [hLT]
    exact fun d hd => L3312.mem_normalizer_sup' (L3312.mem_normalizer_sup' (hD₁ hd) (hD₂ hd))
      (h.DN hd)
  have key : ∀ Y : Subgroup G, Y ∈ lFamilyOf L T → pCoreOf 2 (Y ⊔ T ⊔ D) ≠ ⊥ →
      L3312.Type3312R (↥Y ⧸ CFSG.pCore 2 ↥Y) → ¬ D ≤ Subgroup.normalizer (Y : Set G) →
      IsPSL 2 2 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧ InducesInnerOn T Y ∧
        ∃ K ∈ cComp (Y ⊔ T ⊔ D), Y ≤ K ∧ IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
          Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G) := by
    intro Y hY hO ht hDY
    obtain ⟨K, hK, hYK, hHK, hc⟩ := h12 G T M L D Y h hY hO ht
    rcases hc with hc | ⟨h1, h2, h3⟩
    · exact absurd hc hDY
    · exact ⟨h1, h3, K, hK, hYK, h2, hHK⟩
  by_cases hD₁ : D ≤ Subgroup.normalizer (Y₁ : Set G)
  · have hD₂ : ¬ D ≤ Subgroup.normalizer (Y₂ : Set G) := fun hD₂ => hnot ⟨hD₁, hD₂⟩
    exact ⟨Y₂, Or.inr rfl, hD₂, key Y₂ hY₂ hO₂ ht₂ hD₂⟩
  · exact ⟨Y₁, Or.inl rfl, hD₁, key Y₁ hY₁ hO₁ ht₁ hD₁⟩

end CFSG.Quasithin.H13
