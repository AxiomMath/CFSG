module

public import CFSG.LocalAnalysis.GH72.Sec5OneCore

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}

theorem four_le_card_S₂ : 4 ≤ Nat.card 𝔖.S₂ := by
  obtain ⟨a, ha, ⟨e⟩⟩ := 𝔖.decomp.dih₂
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  omega

theorem exists_bar_S₂_mulEquiv {K : Subgroup G} (hK : 𝔖.S₂ ≤ K) :
    ∃ k : ℕ, 2 ≤ k ∧ Nonempty (bar K 𝔖.S₂ ≃* DihedralGroup (2 ^ k)) := by
  obtain ⟨a, ha, ⟨e⟩⟩ := 𝔖.decomp.dih₂
  obtain ⟨e'⟩ := nonempty_mulEquiv_bar hK (G4c.isPGroup_S₂ 𝔖)
  exact ⟨a, ha, ⟨e'.symm.trans e⟩⟩

omit [Finite G] in
theorem A_le_C (hA : IsE16 A) {t : G} (ht : t ∈ A) : A ≤ C t := fun _ ha =>
  mem_centralizer_singleton_iff.mpr (G4b.comm_of_isE16 hA ha ht)

theorem mem_M_of_mem_X (hA : IsE16 A) {t : G} (ht : t ∈ 𝔖.X A) : t ∈ 𝔖.M A :=
  mem_centralizer_iff.mpr fun _ hx => G4b.comm_of_isE16 hA hx.1 ht.1

variable {𝔖}

include 𝔖 in
theorem sec5_one_M_isolated_X_of
    (h315 : (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧ K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁)))
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (hAS : A ≤ 𝔖.S) (hA : IsE16 A) {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H)
    (hcov : Covers H (𝔖.M₀ A) (O (𝔖.M A)))
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) {t : G}
    (ht : IsIsolatedIn H t) (htX : t ∈ 𝔖.X A) :
    ∃ L₁ : Subgroup (Bar H), H ⊓ 𝔖.M₀ A ≤ H ⊓ 𝔖.M₀ A ∧ 𝔖.Y A ≤ H ⊓ 𝔖.M₀ A ∧
      Covers (H ⊓ 𝔖.M₀ A) (𝔖.M₀ A) (O (𝔖.M A)) ∧
      H ⊓ 𝔖.M₀ A ≤ H ⊓ 𝔖.M₀ A ⊔ (H ⊓ O (𝔖.M A)) ∧
      ((H ⊓ 𝔖.M₀ A ⊔ O H).subgroupOf H).Normal ∧
      O H ⊓ (H ⊓ 𝔖.M₀ A) = H ⊓ 𝔖.M₀ A ⊓ O (𝔖.M A) ∧ IsL2OrA7 (bar H (H ⊓ 𝔖.M₀ A)) 7 ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H (H ⊓ 𝔖.M₀ A) : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H A : Set (Bar H)) ∧
      L₁.Normal ∧ bar H (𝔖.X A) ≤ L₁ ∧ L₁ ⊓ bar H (H ⊓ 𝔖.M₀ A) = ⊥ ∧
      L₁ ≤ centralizer (bar H (H ⊓ 𝔖.M₀ A) : Set (Bar H)) ∧
      (IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) ∧
      L₁ ⊔ bar H (H ⊓ 𝔖.M₀ A) ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ ∧
      (𝔖.S₁ ≤ 𝔖.X A → L₁ = bar H (𝔖.X A)) ∧ (bar H (H ⊓ 𝔖.M₀ A)).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, _, f, hf, hker, hL⟩ := h47.1
  have hLs : IsSimpleGroup L := G4c.isSimpleGroup_of_isL2OrA7' (by norm_num) hL
  have hS₂M₀ : IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) := h47.2.1
  have hOMn : 𝔖.M₀ A ≤ normalizer (O (𝔖.M A) : Set G) :=
    G4c.M₀_le_M.trans (G4c.le_normalizer_O _)
  have hOModd := G4c.odd_card_O (𝔖.M A)
  have hS₂H : 𝔖.S₂ ≤ H := G5one.le_of_covers 𝔖 (Or.inr rfl) hS₂M₀ hOModd hOMn hcov hsyl
  have hS₂W : 𝔖.S₂ ≤ H ⊓ 𝔖.M₀ A := le_inf hS₂H hS₂M₀.le
  have hS₂2 := G4c.isPGroup_S₂ 𝔖
  have hS₂1 : 𝔖.S₂ ≠ ⊥ := by
    intro h
    have := 𝔖.four_le_card_S₂
    rw [h, card_bot] at this
    omega
  have : Finite L := Finite.of_surjective f hf
  obtain ⟨P, hP, hPc⟩ := G5one.exists_isPGroup_card_eq f hker hOModd hS₂M₀.le hS₂2
  have hP1 : P ≠ ⊥ := by
    intro h
    have := 𝔖.four_le_card_S₂
    rw [← hPc, h, card_bot] at this
    omega
  have hLodd := G5one.eq_bot_of_normal_of_odd hP hP1
  have htA : t ∈ A := htX.1
  have ht1 : t ≠ 1 := by
    rintro rfl
    have h := ht.2.1
    rw [orderOf_one] at h
    exact absurd h (by norm_num)
  have hMC : 𝔖.M A ≤ C t := G4c.M_le_C htX
  have hOt : O H ⊓ C t ≤ O (C t) := (𝔖.lemma_4_13_of hA h315 h47 h48 H hH).1 hcov t htX ht1 ht.1
  have hOM : O (𝔖.M A) ≤ O (C t) := by
    have hcovM : Covers (𝔖.M A) (𝔖.M₀ A) (O (𝔖.M A)) := fun x hx =>
      mem_sup_left (mem_inf.mpr ⟨G4c.M₀_le_M hx, hx⟩)
    have h1 := (𝔖.lemma_4_13_of hA h315 h47 h48 (𝔖.M A) (G5one.M_ne_top 𝔖 hAS hA)).1
      hcovM t htX ht1 (𝔖.mem_M_of_mem_X hA htX)
    exact le_trans (le_inf le_rfl ((G4c.O_le _).trans hMC)) h1
  have h5 := h47.2.2.2.2.2 t htX ht1
  have hsupO : (H ⊓ 𝔖.M₀ A) ⊔ O (C t) = ⁅O2 (C t), O2 (C t)⁆ ⊔ O (C t) :=
    G5one.inf_sup_O_eq hMC hOM h5 hcov
  have hWt : H ⊓ 𝔖.M₀ A ≤ H ⊓ C t := inf_le_inf_left _ (G4c.M₀_le_M.trans hMC)
  have hWn : (bar H (H ⊓ 𝔖.M₀ A)).Normal := by
    refine G5one.bar_normal_of_isIsolatedIn ht hWt ?_
    rw [hsupO]
    exact inf_le_right.trans (G5one.le_normalizer_commutator_sup_O (C t))
  have hWf : ((H ⊓ 𝔖.M₀ A).subgroupOf (𝔖.M₀ A)).map f = ⊤ :=
    G5one.map_eq_top_of_isSimpleGroup f hf hker hOModd hOMn hcov inf_le_right le_normalizer
      hS₂W hS₂2 hS₂1
  obtain ⟨hc1, hc2, hc3, hc4, ⟨eW⟩, hc6⟩ :=
    G5one.core f hker hOMn hOModd hLodd inf_le_left inf_le_right hWn hWf
  have hc7 : bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H A : Set (Bar H)) :=
    G5one.bar_inf_le_centralizer_of_sup ((G4b.X_sup_Y 𝔖 hAS hA).symm.trans (sup_comm _ _))
      (G4c.Y_le_S₂.trans hS₂W) (G4c.Y_le_A.trans hAH) (G4c.X_le_A.trans hAH)
      ((G4c.O_le _).trans le_rfl) hc6
  obtain ⟨g, hg, hXg, hYg⟩ := G4c.exists_conj_align hA htA
    (𝔖.fusion.conj₁ t htX.2 𝔖.z₁ 𝔖.hz₁.1 ht.2.1 𝔖.hz₁.2.1) (G4c.S_le_C_z₁ 𝔖)
  obtain ⟨⟨H₁, hRF, hRF', hFR, hTL, -⟩, -⟩ := h315
  have hFK : ⁅H₁, H₁⁆ ≤ H₁ := G4c.commutator_le_of_le le_rfl le_rfl
  have hTK : IsSylowOf 2 (bar (C 𝔖.z₁) 𝔖.S₂) H₁ :=
    G5one.isSylowOf_bar_of_sup 𝔖.S (G4c.S_eq 𝔖) (G4c.S_le_C_z₁ 𝔖) hRF hRF' hFR (hTL.trans hFK)
  have hWF : bar (C 𝔖.z₁) ((H ⊓ 𝔖.M₀ A).map (G4c.cj g)) = ⁅H₁, H₁⁆ :=
    (G5one.bar_map_inf_eq hg hMC hOM h5 hcov).trans
      (G4c.bar_commutator_O2_eq 𝔖.S (G4c.S_eq 𝔖) (G4c.S_le_C_z₁ 𝔖) (G4c.isPGroup_S₁ 𝔖) hRF hRF'
        hFR hTL)
  have hAt : A ≤ H ⊓ C t := le_inf hAH (A_le_C hA htA)
  have hS₁z : 𝔖.S₁ ≤ C 𝔖.z₁ := 𝔖.hz₁.2.2
  have hodd : ∀ x ∈ H₁ ⊓ normalizer (bar (C 𝔖.z₁) 𝔖.S₂ : Set (Bar (C 𝔖.z₁))), Odd (orderOf x) →
      x ∈ normalizer (bar (C 𝔖.z₁) (A.map (G4c.cj g)) : Set (Bar (C 𝔖.z₁))) := by
    obtain ⟨k, hk, ⟨e⟩⟩ := 𝔖.exists_bar_S₂_mulEquiv (G4c.S₂_le_C_z₁ 𝔖)
    refine G5one.mem_normalizer_of_odd e hk ?_ hFR
    rw [← G4b.X_sup_Y 𝔖 hAS hA, G4c.map_cj_sup]
    exact (G4c.bar_mono (sup_le_sup hXg hYg)).trans
      (G4c.bar_sup hS₁z (G4c.S₂_le_C_z₁ 𝔖)).le
  obtain ⟨L₁, hL₁n, hXL, hLW, hLWc, hL2, htop, hLX⟩ :=
    G5one.exists_L_of_isIsolatedIn ht hOt hg hRF hRF' hFR (isPGroup_bar (G4c.isPGroup_S₁ 𝔖))
      hTL hTK (G4c.M₀_le_M.trans hMC) hWF hAt G4c.X_le_A (G4c.bar_mono hXg) hodd
  refine ⟨L₁, le_rfl, G4c.Y_le_S₂.trans hS₂W, hc1, hc2, hc3, hc4,
    isL2OrA7_of_mulEquiv eW hL, hc6, hc7, hL₁n, hXL, hLW, hLWc, Or.inr hL2, htop, fun hS₁X => ?_,
    hWn⟩
  apply hLX
  have hXS : 𝔖.X A = 𝔖.S₁ := le_antisymm G4c.X_le_S₁ hS₁X
  have heq : (𝔖.X A).map (G4c.cj g) = 𝔖.S₁ :=
    eq_of_le_of_card_ge hXg (by rw [G4c.card_map_cj, hXS])
  rw [heq]

include 𝔖 in
theorem sec5_one_M_L₁_of_isSylowOf
    (h44 : ∀ (H : Subgroup G), H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ (A : Subgroup G), A ≤ H → IsE16 A → ∀ (J : Subgroup G), O2 H ⊔ A ≤ J → J ≤ H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) J →
      ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
        bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
        IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₁ ⊓ L₁) L₁ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₂ ⊓ L₂) L₂ ∧
        bar H 𝔖.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔖.S₂ ⊓ bar H J ≤ L₂ ∧
        (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal)
    (h315 : (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧ K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁)))
    (h317 : HasNormalTwoComplement (C (𝔖.z₁ * 𝔖.z₂)))
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (hAS : A ≤ 𝔖.S) (hA : IsE16 A) (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H)
    (hcov : Covers H (𝔖.M₀ A) (O (𝔖.M A)))
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) :
    ∃ W : Subgroup G, ∃ L₁ : Subgroup (Bar H), W ≤ H ⊓ 𝔖.M₀ A ∧ 𝔖.Y A ≤ W ∧
      Covers W (𝔖.M₀ A) (O (𝔖.M A)) ∧ H ⊓ 𝔖.M₀ A ≤ W ⊔ (H ⊓ O (𝔖.M A)) ∧
      ((W ⊔ O H).subgroupOf H).Normal ∧ O H ⊓ W = W ⊓ O (𝔖.M A) ∧ IsL2OrA7 (bar H W) 7 ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H A : Set (Bar H)) ∧ L₁.Normal ∧
      bar H (𝔖.X A) ≤ L₁ ∧ L₁ ⊓ bar H W = ⊥ ∧ L₁ ≤ centralizer (bar H W : Set (Bar H)) ∧
      (IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) ∧
      L₁ ⊔ bar H W ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, _, f, hf, hker, hL⟩ := h47.1
  have hLs : IsSimpleGroup L := G4c.isSimpleGroup_of_isL2OrA7' (by norm_num) hL
  have hS₂M₀ : IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) := h47.2.1
  have hOMn : 𝔖.M₀ A ≤ normalizer (O (𝔖.M A) : Set G) :=
    G4c.M₀_le_M.trans (G4c.le_normalizer_O _)
  have hOModd := G4c.odd_card_O (𝔖.M A)
  have hS₂H : 𝔖.S₂ ≤ H := G5one.le_of_covers 𝔖 (Or.inr rfl) hS₂M₀ hOModd hOMn hcov hsyl
  have hS₂W : 𝔖.S₂ ≤ H ⊓ 𝔖.M₀ A := le_inf hS₂H hS₂M₀.le
  have hS₂2 := G4c.isPGroup_S₂ 𝔖
  have hS₂1 : 𝔖.S₂ ≠ ⊥ := by
    intro h
    have := 𝔖.four_le_card_S₂
    rw [h, card_bot] at this
    omega
  have : Finite L := Finite.of_surjective f hf
  obtain ⟨P, hP, hPc⟩ := G5one.exists_isPGroup_card_eq f hker hOModd hS₂M₀.le hS₂2
  have hP1 : P ≠ ⊥ := by
    intro h
    have := 𝔖.four_le_card_S₂
    rw [← hPc, h, card_bot] at this
    omega
  have hLodd := G5one.eq_bot_of_normal_of_odd hP hP1
  have hXH : 𝔖.X A ≤ H := G4c.X_le_A.trans hAH
  have hYH : 𝔖.Y A ≤ H := G4c.Y_le_A.trans hAH
  have hAXY : A = 𝔖.Y A ⊔ 𝔖.X A := (G4b.X_sup_Y 𝔖 hAS hA).symm.trans (sup_comm _ _)
  by_cases hiso : ∀ t, ¬ IsIsolatedIn H t
  ·
    obtain ⟨L₁, L₂, -, -, hinf, hcent, -, htop, hL₁t, -, -, hsyl₂, hS₁L₁, hS₂L₂, hL₁n, hL₂n⟩ :=
      h44 H hH hiso A hAH hA H (sup_le (G4c.O2_le H) hAH) le_rfl
        (G5one.isSylowOf_sup_inf 𝔖 hsyl (Or.inr hS₂H))
    rw [bar_self] at htop hS₁L₁ hS₂L₂ hL₁n hL₂n
    rw [inf_top_eq] at hS₁L₁ hS₂L₂
    rw [top_inf_eq] at htop
    have hnorm : ∀ L' : Subgroup (Bar H), (L'.subgroupOf ⊤).Normal → L'.Normal := fun L' h =>
      G4c.normal_of_top_le_normalizer ((normal_subgroupOf_iff_le_normalizer le_top).mp h)
    have hL₂n' := hnorm L₂ hL₂n
    have hTL : IsSylowOf 2 (bar H 𝔖.S₂) L₂ := by
      rwa [inf_eq_left.mpr hS₂L₂] at hsyl₂
    have hXL : bar H (𝔖.X A) ≤ L₁ := (G4c.bar_mono G4c.X_le_S₁).trans hS₁L₁
    have hLV : L₂ ≤ centralizer (bar H (𝔖.X A) : Set (Bar H)) :=
      hcent.trans (centralizer_le hXL)
    have hodd : ∀ x ∈ L₂ ⊓ normalizer (bar H 𝔖.S₂ : Set (Bar H)), Odd (orderOf x) →
        x ∈ normalizer (bar H A : Set (Bar H)) := by
      obtain ⟨k, hk, ⟨e⟩⟩ := 𝔖.exists_bar_S₂_mulEquiv hS₂H
      refine G5one.mem_normalizer_of_odd e hk ?_ hLV
      calc bar H A = bar H (𝔖.X A ⊔ 𝔖.Y A) := by rw [G4b.X_sup_Y 𝔖 hAS hA]
        _ = bar H (𝔖.X A) ⊔ bar H (𝔖.Y A) := G4c.bar_sup hXH hYH
        _ ≤ bar H (𝔖.X A) ⊔ bar H 𝔖.S₂ :=
          sup_le_sup_left (G4c.bar_mono (G4c.Y_le_S₂ (𝔖 := 𝔖) (A := A))) _
    obtain ⟨hW₂, hWn, hLW, hLWc, htopW⟩ :=
      G5one.nonisolated (K₀ := 𝔖.M₀ A) hS₂W (hS₂M₀.of_le hS₂W inf_le_right) hXH
        ((G4c.isPGroup_S₁ 𝔖).to_le G4c.X_le_S₁) (G5one.M_le_normalizer_M₀ 𝔖) hL₂n' hinf hcent
        htop hTL hXL hodd
    set W := G5one.genW H (𝔖.M₀ A) 𝔖.S₂ with hWdef
    have hWHK : W ≤ H ⊓ 𝔖.M₀ A := G5one.genW_le hS₂W
    have hWf : (W.subgroupOf (𝔖.M₀ A)).map f = ⊤ :=
      G5one.map_eq_top_of_isSimpleGroup f hf hker hOModd hOMn hcov (hWHK.trans inf_le_right)
        G5one.le_normalizer_genW G5one.le_genW hS₂2 hS₂1
    obtain ⟨hc1, hc2, hc3, hc4, ⟨eW⟩, hc6⟩ :=
      G5one.core f hker hOMn hOModd hLodd (hWHK.trans inf_le_left) (hWHK.trans inf_le_right) hWn
        hWf
    have hYW : 𝔖.Y A ≤ W := G4c.Y_le_S₂.trans G5one.le_genW
    exact ⟨W, L₁, hWHK, hYW, hc1, hc2, hc3, hc4, isL2OrA7_of_mulEquiv eW hL, hc6,
      G5one.bar_inf_le_centralizer_of_sup hAXY hYW hYH hXH (G4c.O_le _) hc6, hnorm L₁ hL₁n, hXL,
      hLW, hLWc, Or.inl hL₁t, htopW⟩
  ·
    push Not at hiso
    obtain ⟨t₀, ht₀⟩ := hiso
    obtain ⟨t, htA, ht⟩ := G5one.exists_isIsolatedIn_mem_A 𝔖 hAS hA hAH hsyl ht₀
    by_cases htX : t ∈ 𝔖.X A
    · obtain ⟨L₁, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -, -⟩ :=
        sec5_one_M_isolated_X_of h315 h47 h48 hAS hA hH hAH hcov hsyl ht htX
      exact ⟨H ⊓ 𝔖.M₀ A, L₁, le_rfl, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
        h15⟩
    · exfalso
      by_cases htY : t ∈ 𝔖.Y A
      · exact G5one.false_of_isIsolatedIn_mem f hf hker hOModd hOMn hcov hS₂M₀.le hS₂2
          𝔖.four_le_card_S₂ ht (hS₂M₀.le (G4c.Y_le_S₂ htY))
      · exact G5one.false_of_isPGroup_bar f hf hker hOModd hOMn hcov hS₂M₀.le hS₂2
          𝔖.four_le_card_S₂ (G5one.isPGroup_bar_of_isIsolatedIn 𝔖 hAS hA h317 ht htA htX htY)

include 𝔖 in
theorem sec5_one_M_L₁_of
    (h44 : ∀ (H : Subgroup G), H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ (A : Subgroup G), A ≤ H → IsE16 A → ∀ (J : Subgroup G), O2 H ⊔ A ≤ J → J ≤ H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) J →
      ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
        bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
        IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₁ ⊓ L₁) L₁ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₂ ⊓ L₂) L₂ ∧
        bar H 𝔖.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔖.S₂ ⊓ bar H J ≤ L₂ ∧
        (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal)
    (h315 : (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧ K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁)))
    (h317 : HasNormalTwoComplement (C (𝔖.z₁ * 𝔖.z₂)))
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (hAS : A ≤ 𝔖.S) (hA : IsE16 A) (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H)
    (hcov : Covers H (𝔖.M₀ A) (O (𝔖.M A))) :
    ∃ W : Subgroup G, ∃ L₁ : Subgroup (Bar H), W ≤ H ⊓ 𝔖.M₀ A ∧ 𝔖.Y A ≤ W ∧
      Covers W (𝔖.M₀ A) (O (𝔖.M A)) ∧ H ⊓ 𝔖.M₀ A ≤ W ⊔ (H ⊓ O (𝔖.M A)) ∧
      ((W ⊔ O H).subgroupOf H).Normal ∧ O H ⊓ W = W ⊓ O (𝔖.M A) ∧ IsL2OrA7 (bar H W) 7 ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H A : Set (Bar H)) ∧ L₁.Normal ∧
      bar H (𝔖.X A) ≤ L₁ ∧ L₁ ⊓ bar H W = ⊥ ∧ L₁ ≤ centralizer (bar H W : Set (Bar H)) ∧
      (IsL2PGL2OrA7OrV4 L₁ ∨ IsPGroup 2 L₁) ∧
      L₁ ⊔ bar H W ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ := by
  obtain ⟨n, hn, hsyl⟩ := G5one.exists_conj_isSylowOf 𝔖 hAS hA hAH
  have hAn : A.map (G4c.cj n) = A := G4c.map_cj_eq_of_mem_normalizer hn
  have hM₀n : (𝔖.M₀ A).map (G4c.cj n) = 𝔖.M₀ A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_M₀ 𝔖 hAS hA hn)
  have hOMn : (O (𝔖.M A)).map (G4c.cj n) = O (𝔖.M A) := by
    rw [G4c.map_cj_O, G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_M 𝔖 hAS hA hn)]
  have hH' : H.map (G4c.cj n) ≠ ⊤ := by
    intro h
    apply hH
    rw [← G4c.map_cj_cj_inv n H, h]
    exact map_top_of_surjective _ (MulAut.conj n⁻¹).surjective
  have hAH' : A ≤ H.map (G4c.cj n) := hAn ▸ map_mono hAH
  have hcov' : Covers (H.map (G4c.cj n)) (𝔖.M₀ A) (O (𝔖.M A)) := by
    have := G5d.covers_map_conj hcov n
    rwa [hM₀n, hOMn] at this
  obtain ⟨W', L₁', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    sec5_one_M_L₁_of_isSylowOf h44 h315 h317 h47 h48 hAS hA _ hH' hAH' hcov' hsyl
  have hn' : n⁻¹ ∈ normalizer (A : Set G) := inv_mem hn
  have hHH : (H.map (G4c.cj n)).map (G4c.cj n⁻¹) = H := G4c.map_cj_cj_inv n H
  have hA' : A.map (G4c.cj n⁻¹) = A := G4c.map_cj_eq_of_mem_normalizer hn'
  have hM₀' : (𝔖.M₀ A).map (G4c.cj n⁻¹) = 𝔖.M₀ A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_M₀ 𝔖 hAS hA hn')
  have hOM' : (O (𝔖.M A)).map (G4c.cj n⁻¹) = O (𝔖.M A) := by
    rw [G4c.map_cj_O,
      G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_M 𝔖 hAS hA hn')]
  have hY' : (𝔖.Y A).map (G4c.cj n⁻¹) = 𝔖.Y A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_Y 𝔖 hAS hA hn')
  have hX' : (𝔖.X A).map (G4c.cj n⁻¹) = 𝔖.X A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_X 𝔖 hAS hA hn')
  obtain ⟨ψ, hψ, t1, t2, t3, t4, t5, t6, t7, t8⟩ :=
    G5one.transport_W hHH hM₀' hOM' hY' hA' ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩
  obtain ⟨L₁, l1, l2, l3, l4, l5, l6⟩ :=
    G5one.transport_L ψ hψ hX' hA' ⟨h10, h11, h12, h13, h14, h15⟩
  obtain ⟨eW⟩ := G5one.nonempty_bar_mulEquiv_of_transport (W := W') ψ hψ
  exact ⟨W'.map (G4c.cj n⁻¹), L₁, t1, t2, t3, t4, t5, t6, isL2OrA7_of_mulEquiv eW h7, t7, t8,
    l1, l2, l3, l4, l5, l6⟩

include 𝔖 in
theorem sec5_one_M_of
    (h44 : ∀ (H : Subgroup G), H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ (A : Subgroup G), A ≤ H → IsE16 A → ∀ (J : Subgroup G), O2 H ⊔ A ≤ J → J ≤ H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) J →
      ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
        bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
        IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₁ ⊓ L₁) L₁ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₂ ⊓ L₂) L₂ ∧
        bar H 𝔖.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔖.S₂ ⊓ bar H J ≤ L₂ ∧
        (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal)
    (h315 : (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧ K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁)))
    (h317 : HasNormalTwoComplement (C (𝔖.z₁ * 𝔖.z₂)))
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (hAS : A ≤ 𝔖.S) (hA : IsE16 A) (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H)
    (hcov : Covers H (𝔖.M₀ A) (O (𝔖.M A))) :
    ∃ W : Subgroup G, W ≤ H ⊓ 𝔖.M₀ A ∧ 𝔖.Y A ≤ W ∧ Covers W (𝔖.M₀ A) (O (𝔖.M A)) ∧
      H ⊓ 𝔖.M₀ A ≤ W ⊔ (H ⊓ O (𝔖.M A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
      O H ⊓ W = W ⊓ O (𝔖.M A) ∧ IsL2OrA7 (bar H W) 7 ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H A : Set (Bar H)) := by
  obtain ⟨W, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ :=
    sec5_one_M_L₁_of h44 h315 h317 h47 h48 hAS hA H hH hAH hcov
  exact ⟨W, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end Sec4Setting

end CFSG.GH72
