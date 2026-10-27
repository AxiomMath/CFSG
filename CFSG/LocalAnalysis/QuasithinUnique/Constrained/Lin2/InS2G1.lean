module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2F3

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

omit [Finite G] in
theorem S₁_le_normalizer_R₁ {M₀ S L : Subgroup G} :
    s2S₁ M₀ S L ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) := inf_le_right

namespace S2Ok

variable {D₁ D₂ : Subgroup G} (O : S2Ok T M H S L D n t M₀ x₀ q W D₁ D₂)
include O

theorem L₂_not_le_M : ¬ conjR L t ≤ M := by
  have hB := O.base
  intro h
  apply hB.cs.not_le
  have h1 := conjR_mono h t⁻¹
  rw [conjR_conjR_inv, conjR_eq_of_mem (M.inv_mem (hB.S_le_M hB.ht))] at h1
  exact h1

theorem L₂_le_normalizer_R₁ : conjR L t ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
  le_normalizer_of_commute fun a ha b hb => O.base.comm_elem a ha.2 b hb

theorem R1_le_normalizer_R₁ : AppE.R1 S L ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
  fun _ hg => conjR_eq_self_iff.1 (mem_s2S₁.1 (O.base.R1_le_S₁ hg)).2

theorem R₁_isPGroup : IsPGroup 2 ↥(thompsonJ S ⊓ L) :=
  O.base.R_isPGroup.to_le inf_le_left

theorem R₁_le_pCore {K : Subgroup G} (hK : K ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G))
    (hR₁K : thompsonJ S ⊓ L ≤ K) : thompsonJ S ⊓ L ≤ pCoreOf 2 K :=
  le_pCoreOf_of_normalizes hR₁K hK O.R₁_isPGroup

theorem pCore_ne_bot_of {K : Subgroup G} (hK : K ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G))
    (hR₁K : thompsonJ S ⊓ L ≤ K) : pCoreOf 2 K ≠ ⊥ := fun h => by
  have := O.R₁_le_pCore hK hR₁K
  rw [h] at this
  exact O.base.R₁_ne_bot (le_bot_iff.1 this)

theorem witnessPair₀ : IsWitnessPair M (AppE.R1 S L) (conjR L t ⊔ AppE.R1 S L) := by
  have hB := O.base
  have hle : conjR L t ⊔ AppE.R1 S L ≤
      Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
    sup_le O.L₂_le_normalizer_R₁ O.R1_le_normalizer_R₁
  have hR₁K : thompsonJ S ⊓ L ≤ conjR L t ⊔ AppE.R1 S L := R₁_le_R1.trans le_sup_right
  have hHle : conjR L t ⊔ AppE.R1 S L ≤ H :=
    sup_le (hB.L₂_le_L₀.trans hB.L₀_le_H) (AppE.R1_le_S.trans hB.S_le_H)
  refine ⟨hB.isConfining_R1, le_sup_right, O.pCore_ne_bot_of hle hR₁K, ?_, ?_⟩
  · exact charTwo_of_pCore_centralizer_le hB.cs.charTwo hHle fun y hy =>
      (le_sup_right : AppE.R1 S L ≤ conjR L t ⊔ AppE.R1 S L) (hB.dbl.pCoreOf_le_R1 hy.1)
  · exact fun h => O.L₂_not_le_M (le_sup_left.trans h)

end S2Ok

end CFSG.QuasithinUnique.Lin2
