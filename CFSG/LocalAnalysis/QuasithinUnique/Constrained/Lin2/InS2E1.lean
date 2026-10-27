module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2D3
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraConfining

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

@[expose] def s2S₁ (M₀ S L : Subgroup G) : Subgroup G :=
  M₀ ⊓ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G)

omit [Finite G] in
theorem mem_s2S₁ {M₀ S L : Subgroup G} {g : G} :
    g ∈ s2S₁ M₀ S L ↔ g ∈ M₀ ∧ conjR (thompsonJ S ⊓ L) g = thompsonJ S ⊓ L :=
  and_congr_right fun _ => conjR_eq_self_iff.symm

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem R₁_ne_bot : thompsonJ S ⊓ L ≠ ⊥ := by
  intro h
  have h1 : blockU L ≤ thompsonJ S ⊓ L := le_inf B.U₁_le_R (blockU_le L)
  rw [h, le_bot_iff] at h1
  have := one_lt_card_blockU B.hlin B.hn
  rw [h1, Subgroup.card_bot] at this
  omega

theorem R₁_eq_centralizer {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) :
    thompsonJ S ⊓ L = thompsonJ S ⊓ Subgroup.centralizer (D₂ : Set G) := by
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  have h4 : 4 ≤ 2 ^ n := two_pow_ge_four B.hn
  apply le_antisymm
  · rintro r ⟨hrR, hrL⟩
    refine ⟨hrR, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
    exact (B.comm_elem r hrL d (hD₂L hd)).symm
  · rintro r ⟨hrR, hrC⟩
    obtain ⟨d₂, hd₂, hd₂1⟩ := exists_ne_one_of_one_lt_card (X := D₂) (by rw [hT₂.card]; omega)
    have hdD : d₂ ∈ D := hD ▸ Subgroup.mem_sup_right hd₂
    have hdD₁ : d₂ ∉ D₁ := by
      intro h
      have : d₂ ∈ L ⊓ conjR L t := ⟨hD₁L h, hD₂L hd₂⟩
      rw [B.L_inf_L₂, Subgroup.mem_bot] at this
      exact hd₂1 this
    have hle := B.cent_elem_le_R₁ hT₁ hT₂ hD hC hdD hdD₁
    exact (hle ⟨hrR, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hrC d₂ hd₂).symm⟩)

theorem R₂_eq_centralizer {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) :
    thompsonJ S ⊓ conjR L t = thompsonJ S ⊓ Subgroup.centralizer (D₁ : Set G) := by
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  have h4 : 4 ≤ 2 ^ n := two_pow_ge_four B.hn
  apply le_antisymm
  · rintro r ⟨hrR, hrL⟩
    refine ⟨hrR, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
    exact B.comm_elem d (hD₁L hd) r hrL
  · rintro r ⟨hrR, hrC⟩
    obtain ⟨d₁, hd₁, hd₁1⟩ := exists_ne_one_of_one_lt_card (X := D₁) (by rw [hT₁.card]; omega)
    have hdD : d₁ ∈ D := hD ▸ Subgroup.mem_sup_left hd₁
    have hdD₂ : d₁ ∉ D₂ := by
      intro h
      have : d₁ ∈ L ⊓ conjR L t := ⟨hD₁L hd₁, hD₂L h⟩
      rw [B.L_inf_L₂, Subgroup.mem_bot] at this
      exact hd₁1 this
    have hle := B.cent_elem_le_R₂ hT₁ hT₂ hD hC hdD hdD₂
    exact (hle ⟨hrR, Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hrC d₁ hd₁).symm⟩)

theorem conjR_R₁ {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x₀ = D) :
    conjR (thompsonJ S ⊓ L) x₀ = thompsonJ S ⊓ L := by
  rw [B.R₁_eq_centralizer hT₁ hT₂ hD hC, conjR_inf, B.conjR_R_x₀, ← conjR_centralizer,
    B.conjR_D₂_eq_self hT₁ hT₂ hD hC hDx]

theorem conjR_R₂ {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x₀ = D) :
    conjR (thompsonJ S ⊓ conjR L t) x₀ = thompsonJ S ⊓ conjR L t := by
  rw [B.R₂_eq_centralizer hT₁ hT₂ hD hC, conjR_inf, B.conjR_R_x₀, ← conjR_centralizer,
    B.conjR_D₁_eq_self hT₁ hT₂ hD hC hDx]

theorem M₀_le_normalizer_R : M₀ ≤ Subgroup.normalizer (thompsonJ S : Set G) := fun _ hg =>
  GammaExtra.normalizer_le_normalizer_thompsonJ S (normalizer_of_relIndex_two B.hSM B.h2 hg)

theorem isConfining_R1 : IsConfining M (AppE.R1 S L) :=
  IsGamma0.isConfining_of_relIndex_two B.cs.setting B.cs.gamma0 B.cs.sylow_inf
    B.dbl.thompsonJ_le_R1 AppE.R1_le_S B.dbl.relIndex_R1
    (IsGamma0.pCore_centralizer_le_of_charTwo B.cs.setting B.cs.gamma0 B.cs.sylow_inf
      B.cs.charTwo B.dbl.pCoreOf_le_R1)

theorem x₀_mem_S₁ {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x₀ = D) : x₀ ∈ s2S₁ M₀ S L :=
  mem_s2S₁.2 ⟨B.hx₀, B.conjR_R₁ hT₁ hT₂ hD hC hDx⟩

theorem S_inf_S₁ : S ⊓ s2S₁ M₀ S L = AppE.R1 S L := by
  ext g
  constructor
  · rintro ⟨hgS, hg⟩
    obtain ⟨hgM, hgR₁⟩ := mem_s2S₁.1 hg
    rw [AppE.mem_R1_iff]
    refine ⟨hgS, ?_⟩
    by_contra hne
    have hnot : g ∉ AppE.R1 S L := fun h => hne (AppE.mem_R1_iff.1 h).2
    have hgL : conjR L g = conjR L t := B.dbl.conjR_eq_t_of_not_mem hgS hnot
    have hgR : conjR (thompsonJ S) g = thompsonJ S :=
      thompsonJ_normalized (Subgroup.le_normalizer hgS)
    have h1 : conjR (thompsonJ S ⊓ L) g = thompsonJ S ⊓ conjR L t := by
      rw [conjR_inf, hgR, hgL]
    have h4 : thompsonJ S ⊓ L = thompsonJ S ⊓ conjR L t := hgR₁.symm.trans h1
    have h3 : thompsonJ S ⊓ L ≤ ⊥ := by
      rw [← B.L_inf_L₂]
      exact le_inf inf_le_right (h4 ▸ inf_le_right)
    exact B.R₁_ne_bot (le_bot_iff.1 h3)
  · intro hg
    obtain ⟨hgS, hgL⟩ := AppE.mem_R1_iff.1 hg
    refine ⟨hgS, mem_s2S₁.2 ⟨B.hSM hgS, ?_⟩⟩
    rw [conjR_inf, thompsonJ_normalized (Subgroup.le_normalizer hgS), hgL]

theorem R1_le_S₁ : AppE.R1 S L ≤ s2S₁ M₀ S L := B.S_inf_S₁ ▸ inf_le_right

theorem S₁_le_T : s2S₁ M₀ S L ≤ T := inf_le_left.trans B.hMT

theorem S₁_isPGroup : IsPGroup 2 (s2S₁ M₀ S L) := B.T_isPGroup.to_le B.S₁_le_T

theorem relIndex_R1_S₁ {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x₀ = D) :
    (AppE.R1 S L).relIndex (s2S₁ M₀ S L) = 2 := by
  show ((AppE.R1 S L).subgroupOf (s2S₁ M₀ S L)).index = 2
  rw [Subgroup.index_eq_two_iff]
  have hx₁ : x₀ ∈ s2S₁ M₀ S L := B.x₀_mem_S₁ hT₁ hT₂ hD hC hDx
  refine ⟨⟨x₀, hx₁⟩, fun b => ?_⟩
  have hb := b.2
  obtain ⟨hbM, -⟩ := mem_s2S₁.1 hb
  show Xor (b * ⟨x₀, hx₁⟩ ∈ (AppE.R1 S L).subgroupOf _) (b ∈ (AppE.R1 S L).subgroupOf _)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hbS : (b : G) ∈ S
  · have hbR : (b : G) ∈ AppE.R1 S L := by rw [← B.S_inf_S₁]; exact ⟨hbS, hb⟩
    have h1 : (b : G) * x₀ ∉ AppE.R1 S L := by
      intro h
      apply B.hx₀S
      have := (AppE.R1 S L).mul_mem ((AppE.R1 S L).inv_mem hbR) h
      simpa using AppE.R1_le_S this
    exact Or.inr ⟨hbR, h1⟩
  · have hbn : (b : G) ∉ AppE.R1 S L := fun h => hbS (AppE.R1_le_S h)
    have h2 : (b : G)⁻¹⁻¹ * x₀ ∈ S :=
      CFSG.QuasithinUnique.inv_mul_mem_of_relIndex_two B.h2 (M₀.inv_mem hbM)
        (fun h => hbS (by simpa using S.inv_mem h)) B.hx₀ B.hx₀S
    rw [inv_inv] at h2
    have h3 : (b : G) * x₀ ∈ AppE.R1 S L := by
      rw [← B.S_inf_S₁]
      exact ⟨h2, (s2S₁ M₀ S L).mul_mem hb hx₁⟩
    exact Or.inl ⟨h3, hbn⟩

theorem card_S₁ {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x₀ = D) :
    Nat.card (s2S₁ M₀ S L) = Nat.card S := by
  have h1 := Subgroup.relIndex_mul_card (H := AppE.R1 S L) (K := s2S₁ M₀ S L)
  rw [inf_eq_left.2 B.R1_le_S₁, B.relIndex_R1_S₁ hT₁ hT₂ hD hC hDx] at h1
  have h2 := GammaExtra.card_eq_two_mul_of_relIndex_eq_two AppE.R1_le_S B.dbl.relIndex_R1
  rw [h2, ← h1]

end S2Base

end CFSG.QuasithinUnique.Lin2
