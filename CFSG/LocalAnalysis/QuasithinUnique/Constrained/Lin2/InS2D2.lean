module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2D1

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

theorem one_lt_card_blockU {Lb : Subgroup G} {n : ℕ} (hlin : IsLin2Type Lb n) (hn : 2 ≤ n) :
    1 < Nat.card (blockU Lb) := by
  rw [lin2_card_U hlin]
  have h4 := two_pow_ge_four hn
  have h16 : 16 ≤ 2 ^ (2 * n) :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < Nat.card (blockZ Lb) := Nat.card_pos
  nlinarith

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem blockZ_eq_bot (hC : baumD S L = ⊥) : blockZ L = ⊥ :=
  le_bot_iff.1 (hC ▸ B.blockZ_le_C)

theorem blockZ₂_eq_bot (hC : baumD S L = ⊥) : blockZ (conjR L t) = ⊥ :=
  le_bot_iff.1 (hC ▸ B.blockZ_le_C₂)

theorem R_eq_R₁R₂ (hC : baumD S L = ⊥) :
    thompsonJ S = (thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ conjR L t) := by
  have h := B.R_eq_sup
  rwa [B.C_eq_baumD, hC, sup_bot_eq] at h

theorem pCore_eq_UU (hC : baumD S L = ⊥) :
    pCoreOf 2 H = blockU L ⊔ conjSubgroup (blockU L) t := by
  rw [B.su.O_eq_DU, hC, bot_sup_eq]

theorem cent_elem_le_R₁ {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) {d : G} (hd : d ∈ D) (hd1 : d ∉ D₁) :
    thompsonJ S ⊓ Subgroup.centralizer ({d} : Set G) ≤ thompsonJ S ⊓ L := by
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  rintro r ⟨hrR, hrd⟩
  obtain ⟨r₁, hr₁, r₂, hr₂, c, hc, rfl⟩ := B.R_decomp r hrR
  have hc1 : c = 1 := by rw [hC] at hc; exact Subgroup.mem_bot.1 hc
  subst hc1
  rw [mul_one] at hrd ⊢
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := B.D_decomp hD₁L hD₂L hD d hd
  have hd₂1 : d₂ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hd1
    exact hd1 hd₁
  have hcomm : d₁ * d₂ * (r₁ * r₂) = (r₁ * r₂) * (d₁ * d₂) :=
    (Subgroup.mem_centralizer_singleton_iff.1 hrd).symm
  have hdr₁ : d₂ * r₁ = r₁ * d₂ := (B.comm_elem r₁ hr₁.2 d₂ (hD₂L hd₂)).symm
  have hdr₂ : r₂ * d₁ = d₁ * r₂ := (B.comm_elem d₁ (hD₁L hd₁) r₂ hr₂.2).symm
  have hcomp : (d₁ * r₁) * (d₂ * r₂) = (r₁ * d₁) * (r₂ * d₂) := by
    calc (d₁ * r₁) * (d₂ * r₂) = d₁ * (r₁ * d₂) * r₂ := by group
      _ = d₁ * (d₂ * r₁) * r₂ := by rw [hdr₁]
      _ = d₁ * d₂ * (r₁ * r₂) := by group
      _ = (r₁ * r₂) * (d₁ * d₂) := hcomm
      _ = r₁ * (r₂ * d₁) * d₂ := by group
      _ = r₁ * (d₁ * r₂) * d₂ := by rw [hdr₂]
      _ = (r₁ * d₁) * (r₂ * d₂) := by group
  have hX : d₁ * r₁ ∈ L := L.mul_mem (hD₁L hd₁) hr₁.2
  have hX' : r₁ * d₁ ∈ L := L.mul_mem hr₁.2 (hD₁L hd₁)
  have hY : d₂ * r₂ ∈ conjR L t := (conjR L t).mul_mem (hD₂L hd₂) hr₂.2
  have hY' : r₂ * d₂ ∈ conjR L t := (conjR L t).mul_mem hr₂.2 (hD₂L hd₂)
  have h2 := (exists_unique_of_inf_bot B.L_inf_L₂ hX hX' hY hY' hcomp).2
  have hz : r₂ ∈ blockZ (conjR L t) := torus_comm_mem_Z hT₂ B.pCore_L₂ hd₂ hd₂1 hr₂ h2
  rw [B.blockZ₂_eq_bot hC, Subgroup.mem_bot] at hz
  rw [hz, mul_one]
  exact hr₁

theorem cent_elem_le_R₂ {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) {d : G} (hd : d ∈ D) (hd2 : d ∉ D₂) :
    thompsonJ S ⊓ Subgroup.centralizer ({d} : Set G) ≤ thompsonJ S ⊓ conjR L t := by
  have hD₁L : D₁ ≤ L := hT₁.le_borel.trans inf_le_left
  have hD₂L : D₂ ≤ conjR L t := hT₂.le_borel.trans inf_le_left
  rintro r ⟨hrR, hrd⟩
  obtain ⟨r₁, hr₁, r₂, hr₂, c, hc, rfl⟩ := B.R_decomp r hrR
  have hc1 : c = 1 := by rw [hC] at hc; exact Subgroup.mem_bot.1 hc
  subst hc1
  rw [mul_one] at hrd ⊢
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := B.D_decomp hD₁L hD₂L hD d hd
  have hd₁1 : d₁ ≠ 1 := by
    rintro rfl
    rw [one_mul] at hd2
    exact hd2 hd₂
  have hcomm : d₁ * d₂ * (r₁ * r₂) = (r₁ * r₂) * (d₁ * d₂) :=
    (Subgroup.mem_centralizer_singleton_iff.1 hrd).symm
  have hdr₁ : d₂ * r₁ = r₁ * d₂ := (B.comm_elem r₁ hr₁.2 d₂ (hD₂L hd₂)).symm
  have hdr₂ : r₂ * d₁ = d₁ * r₂ := (B.comm_elem d₁ (hD₁L hd₁) r₂ hr₂.2).symm
  have hcomp : (d₁ * r₁) * (d₂ * r₂) = (r₁ * d₁) * (r₂ * d₂) := by
    calc (d₁ * r₁) * (d₂ * r₂) = d₁ * (r₁ * d₂) * r₂ := by group
      _ = d₁ * (d₂ * r₁) * r₂ := by rw [hdr₁]
      _ = d₁ * d₂ * (r₁ * r₂) := by group
      _ = (r₁ * r₂) * (d₁ * d₂) := hcomm
      _ = r₁ * (r₂ * d₁) * d₂ := by group
      _ = r₁ * (d₁ * r₂) * d₂ := by rw [hdr₂]
      _ = (r₁ * d₁) * (r₂ * d₂) := by group
  have hX : d₁ * r₁ ∈ L := L.mul_mem (hD₁L hd₁) hr₁.2
  have hX' : r₁ * d₁ ∈ L := L.mul_mem hr₁.2 (hD₁L hd₁)
  have hY : d₂ * r₂ ∈ conjR L t := (conjR L t).mul_mem (hD₂L hd₂) hr₂.2
  have hY' : r₂ * d₂ ∈ conjR L t := (conjR L t).mul_mem hr₂.2 (hD₂L hd₂)
  have h1 := (exists_unique_of_inf_bot B.L_inf_L₂ hX hX' hY hY' hcomp).1
  have hz : r₁ ∈ blockZ L := torus_comm_mem_Z hT₁ B.pCore_L hd₁ hd₁1 hr₁ h1
  rw [B.blockZ_eq_bot hC, Subgroup.mem_bot] at hz
  rw [hz, one_mul]
  exact hr₂

theorem sub_D_le_or {D₁ D₂ : Subgroup G} (hT₁ : BlockTorus L (thompsonJ S ⊓ L) D₁ n)
    (hT₂ : BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n) (hD : D = D₁ ⊔ D₂)
    (hC : baumD S L = ⊥) {E : Subgroup G} (hED : E ≤ D)
    (hE : ∀ g ∈ E, g ≠ 1 → thompsonJ S ⊓ Subgroup.centralizer ({g} : Set G) ≠ ⊥) :
    E ≤ D₁ ∨ E ≤ D₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hcon₁, hcon₂⟩ := hcon
  obtain ⟨a, haE, haD₁⟩ : ∃ a ∈ E, a ∉ D₁ := by
    by_contra h
    push Not at h
    exact hcon₁ h
  obtain ⟨b, hbE, hbD₂⟩ : ∃ b ∈ E, b ∉ D₂ := by
    by_contra h
    push Not at h
    exact hcon₂ h
  have hbot : ∀ g ∈ E, g ∉ D₁ → g ∉ D₂ → False := by
    intro g hgE hg1 hg2
    apply hE g hgE (fun h => hg1 (h ▸ D₁.one_mem))
    rw [eq_bot_iff, ← B.R₁_inf_R₂]
    exact le_inf (B.cent_elem_le_R₁ hT₁ hT₂ hD hC (hED hgE) hg1)
      (B.cent_elem_le_R₂ hT₁ hT₂ hD hC (hED hgE) hg2)
  have ha : a ∈ D₂ := by
    by_contra h; exact hbot a haE haD₁ h
  have hb : b ∈ D₁ := by
    by_contra h; exact hbot b hbE h hbD₂
  by_cases hab : a * b ∈ D₁
  · apply haD₁
    have := D₁.mul_mem hab (D₁.inv_mem hb)
    simpa using this
  · have hab2 : a * b ∈ D₂ := by
      by_contra h; exact hbot (a * b) (E.mul_mem haE hbE) hab h
    apply hbD₂
    have := D₂.mul_mem (D₂.inv_mem ha) hab2
    simpa using this

end S2Base

end CFSG.QuasithinUnique.Lin2
