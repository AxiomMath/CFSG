module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2D2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem U₁_le_R : blockU L ≤ thompsonJ S := by
  rw [← B.baum_eq]; exact B.su.U₁_le_B

theorem U₂_le_R : blockU (conjR L t) ≤ thompsonJ S := by
  rw [DoubleA3.blockU_conjR, ← B.baum_eq]; exact B.su.U₂_le_B

theorem conjR_D₁_cases {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x₀ = D) : conjR D₁ x₀ = D₁ ∨ conjR D₁ x₀ = D₂ := by
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₁D : D₁ ≤ D := hD ▸ le_sup_left
  have hle : conjR D₁ x₀ ≤ D := by
    have := conjR_mono hD₁D x₀
    rwa [hDx] at this
  have hE : ∀ g ∈ conjR D₁ x₀, g ≠ 1 →
      thompsonJ S ⊓ Subgroup.centralizer ({g} : Set G) ≠ ⊥ := by
    intro g hg hg1
    obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hg
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_one_lt_card (X := blockU (conjR L t))
      (one_lt_card_blockU B.hlin₂ B.hn)
    have hz : x₀⁻¹ * u * x₀ ∈ conjR (thompsonJ S) x₀ := mem_conjR_iff'.2 ⟨u, B.U₂_le_R hu, rfl⟩
    rw [B.conjR_R_x₀] at hz
    have hcomm : d * u = u * d := B.comm_elem d (hD₁L hd) u (blockU_le _ hu)
    have hzc : x₀⁻¹ * u * x₀ ∈ Subgroup.centralizer ({x₀⁻¹ * d * x₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x₀⁻¹ * u * x₀ * (x₀⁻¹ * d * x₀) = x₀⁻¹ * (u * d) * x₀ := by group
        _ = x₀⁻¹ * (d * u) * x₀ := by rw [hcomm]
        _ = x₀⁻¹ * d * x₀ * (x₀⁻¹ * u * x₀) := by group
    intro h
    have hmem : x₀⁻¹ * u * x₀ ∈ (⊥ : Subgroup G) := h ▸ (⟨hz, hzc⟩ : _ ∈ thompsonJ S ⊓ _)
    rw [Subgroup.mem_bot] at hmem
    apply hu1
    have := congrArg (fun w => x₀ * w * x₀⁻¹) hmem
    simpa [mul_assoc] using this
  rcases B.sub_D_le_or hT₁ hT₂ hD hC hle hE with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (card_conjR D₁ x₀).ge)
  · refine Or.inr (Subgroup.eq_of_le_of_card_ge h ?_)
    rw [hT₂.card, card_conjR, hT₁.card]

theorem conjR_D₂_cases {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x₀ = D) : conjR D₂ x₀ = D₁ ∨ conjR D₂ x₀ = D₂ := by
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  have hD₂D : D₂ ≤ D := hD ▸ le_sup_right
  have hle : conjR D₂ x₀ ≤ D := by
    have := conjR_mono hD₂D x₀
    rwa [hDx] at this
  have hE : ∀ g ∈ conjR D₂ x₀, g ≠ 1 →
      thompsonJ S ⊓ Subgroup.centralizer ({g} : Set G) ≠ ⊥ := by
    intro g hg hg1
    obtain ⟨d, hd, rfl⟩ := mem_conjR_iff'.1 hg
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_one_lt_card (X := blockU L)
      (one_lt_card_blockU B.hlin B.hn)
    have hz : x₀⁻¹ * u * x₀ ∈ conjR (thompsonJ S) x₀ := mem_conjR_iff'.2 ⟨u, B.U₁_le_R hu, rfl⟩
    rw [B.conjR_R_x₀] at hz
    have hcomm : u * d = d * u := B.comm_elem u (blockU_le _ hu) d (hD₂L hd)
    have hzc : x₀⁻¹ * u * x₀ ∈ Subgroup.centralizer ({x₀⁻¹ * d * x₀} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x₀⁻¹ * u * x₀ * (x₀⁻¹ * d * x₀) = x₀⁻¹ * (u * d) * x₀ := by group
        _ = x₀⁻¹ * (d * u) * x₀ := by rw [hcomm]
        _ = x₀⁻¹ * d * x₀ * (x₀⁻¹ * u * x₀) := by group
    intro h
    have hmem : x₀⁻¹ * u * x₀ ∈ (⊥ : Subgroup G) := h ▸ (⟨hz, hzc⟩ : _ ∈ thompsonJ S ⊓ _)
    rw [Subgroup.mem_bot] at hmem
    apply hu1
    have := congrArg (fun w => x₀ * w * x₀⁻¹) hmem
    simpa [mul_assoc] using this
  rcases B.sub_D_le_or hT₁ hT₂ hD hC hle hE with h | h
  · refine Or.inl (Subgroup.eq_of_le_of_card_ge h ?_)
    rw [hT₁.card, card_conjR, hT₂.card]
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (card_conjR D₂ x₀).ge)

theorem conjR_D₁_eq_self {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x₀ = D) : conjR D₁ x₀ = D₁ := by
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  have hD₁D : D₁ ≤ D := hD ▸ le_sup_left
  have h4 := two_pow_ge_four B.hn
  rcases B.conjR_D₁_cases hT₁ hT₂ hD hC hDx with h | h
  · exact h
  exfalso
  rcases B.conjR_D₂_cases hT₁ hT₂ hD hC hDx with h' | h'
  ·
    apply B.su.good
    have hU₁ : blockU L ≤ thompsonJ S ⊓ Subgroup.centralizer (D₂ : Set G) := by
      intro u hu
      refine ⟨B.U₁_le_R hu, Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
      exact (B.comm_elem u (blockU_le L hu) d (hD₂L hd)).symm
    have h1 := conjR_mono hU₁ x₀
    rw [conjR_inf, B.conjR_R_x₀, ← conjR_centralizer, h'] at h1
    refine h1.trans ?_
    obtain ⟨d₁, hd₁, hd₁1⟩ := exists_ne_one_of_one_lt_card (X := D₁) (by rw [hT₁.card]; omega)
    have hd₁₂ : d₁ ∉ D₂ := by
      intro hd2
      have : d₁ ∈ L ⊓ conjR L t := ⟨hD₁L hd₁, hD₂L hd2⟩
      rw [B.L_inf_L₂, Subgroup.mem_bot] at this
      exact hd₁1 this
    have hle := B.cent_elem_le_R₂ hT₁ hT₂ hD hC (hD₁D hd₁) hd₁₂
    rintro r ⟨hrR, hrC⟩
    have hrL₂ : r ∈ conjR L t := (hle ⟨hrR,
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hrC d₁ hd₁).symm⟩).2
    refine ⟨B.baum_eq ▸ hrR, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
    exact B.comm_elem u (blockU_le L hu) r hrL₂
  ·
    have : D₁ = D₂ := conjR_inj_right (h.trans h'.symm)
    obtain ⟨d₁, hd₁, hd₁1⟩ := exists_ne_one_of_one_lt_card (X := D₁) (by rw [hT₁.card]; omega)
    have : d₁ ∈ L ⊓ conjR L t := ⟨hD₁L hd₁, hD₂L (by rwa [← this])⟩
    rw [B.L_inf_L₂, Subgroup.mem_bot] at this
    exact hd₁1 this

theorem conjR_D₂_eq_self {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) (hDx : conjR D x₀ = D) : conjR D₂ x₀ = D₂ := by
  have h1 := B.conjR_D₁_eq_self hT₁ hT₂ hD hC hDx
  rcases B.conjR_D₂_cases hT₁ hT₂ hD hC hDx with h | h
  ·
    exact absurd (conjR_inj_right (h.trans h1.symm)) (by
      intro hne
      have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
      have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
      have h4 := two_pow_ge_four B.hn
      obtain ⟨d₁, hd₁, hd₁1⟩ := exists_ne_one_of_one_lt_card (X := D₁) (by rw [hT₁.card]; omega)
      have : d₁ ∈ L ⊓ conjR L t := ⟨hD₁L hd₁, hD₂L (by rwa [hne])⟩
      rw [B.L_inf_L₂, Subgroup.mem_bot] at this
      exact hd₁1 this)
  · exact h

end S2Base

end CFSG.QuasithinUnique.Lin2
