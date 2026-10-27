module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.T1531Stage1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Stage15344_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp : Subgroup G) (t : G),
    Hyp15310 G T Mc M V₁ V₂ Yp t → IsUniqueM (Yp ⊔ Sgp153 T V₁) M

section Proof

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem unique_centralizer_Y153_F4 (h44 : Stage15344_F4) (c : Ctx153 G T Mc M V₁ V₂ t) :
    IsUniqueM ((Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ⊔ Sgp153 T V₁) M := by
  have hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M :=
    h44 G T Mc M V₁ V₂ (Y153 Mc M) t ⟨c.hyp, c.decomp, Or.inl rfl⟩
  have h2 := h44 G T Mc M V₁ V₂ (oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) t
    ⟨c.hyp, c.decomp, Or.inr ⟨hU, rfl⟩⟩
  refine isUniqueM_mono h2 (sup_le_sup_right (oTwoUpper_le _) _) ?_
  exact sup_le (inf_le_left.trans (Y153_le Mc M)) (inf_le_left.trans c.hyp.T_le)

theorem lemma_15_3_45_F4 (h44 : Stage15344_F4) (h113 : StageLemma14113)
    (c : Ctx153 G T Mc M V₁ V₂ t) : Res15345 T Mc M V₁ V₂ := by
  have hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M :=
    h44 G T Mc M V₁ V₂ (Y153 Mc M) t ⟨c.hyp, c.decomp, Or.inl rfl⟩
  have cs : Ctx153 G T Mc M V₂ V₁ t := ⟨c.hyp, c.decomp.swapPlanes⟩
  have hS₂ : Sgp153 T V₂ = Sgp153 T V₁ := c.hyp.Sgp153_eq_inf_normalizer_V₂ c.decomp
  have u₁ := unique_centralizer_Y153_F4 h44 c
  have u₂ : IsUniqueM ((Y153 Mc M ⊓ Subgroup.centralizer (V₂ : Set G)) ⊔ Sgp153 T V₁) M := by
    have := unique_centralizer_Y153_F4 h44 cs
    rwa [hS₂] at this
  have hn := c.hyp.normalizer_V_le h113 c.decomp hU
  have hN₁ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₁ : Set G) := inf_le_right
  have hN₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    c.hyp.Sgp153_le_normalizer_V₂ c.decomp
  have hV₁ : V₁ ≠ ⊥ := by
    intro hb
    have := c.decomp.card₁
    rw [hb, Subgroup.card_bot] at this
    omega
  have hV₂ : V₂ ≠ ⊥ := by
    intro hb
    have := c.decomp.card₂
    rw [hb, Subgroup.card_bot] at this
    omega
  exact ⟨u₁, u₂, hn.1, hn.2, centralizer_le_of_isUniqueM c c.decomp.le₁ hV₁ hN₁ u₁,
    centralizer_le_of_isUniqueM c c.decomp.le₂ hV₂ hN₂ u₂⟩

end Proof

end CFSG.Quasithin
