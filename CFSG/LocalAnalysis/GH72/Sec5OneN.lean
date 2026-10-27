module

public import CFSG.LocalAnalysis.GH72.Sec5OneCore
public import CFSG.LocalAnalysis.GH72.Sec4FourBasic

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open G5one

namespace Sec4Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}

theorem four_le_card_S₁ : 4 ≤ Nat.card 𝔖.S₁ := by
  obtain ⟨a, ha, ⟨e⟩⟩ := 𝔖.decomp.dih₁
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  omega

theorem sec5_one_N_of_W (hAS : A ≤ 𝔖.S) (hA : IsE16 A) {L : Type} [Group L]
    (f : 𝔖.N₀ A →* L) (hker : f.ker = (O (𝔖.N A)).subgroupOf (𝔖.N₀ A))
    (hLt : IsL2OrA7 L 5 ∨ IsKleinFour L)
    (hLodd : ∀ N : Subgroup L, N.Normal → Odd (Nat.card N) → N = ⊥)
    {H W : Subgroup G} (hAH : A ≤ H) (hWH : W ≤ H) (hWN : W ≤ 𝔖.N₀ A) (hXW : 𝔖.X A ≤ W)
    (hWn : (bar H W).Normal) (hWf : (W.subgroupOf (𝔖.N₀ A)).map f = ⊤) :
    W ≤ H ⊓ 𝔖.N₀ A ∧ 𝔖.X A ≤ W ∧ Covers W (𝔖.N₀ A) (O (𝔖.N A)) ∧
      H ⊓ 𝔖.N₀ A ≤ W ⊔ (H ⊓ O (𝔖.N A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
      O H ⊓ W = W ⊓ O (𝔖.N A) ∧
      (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H (𝔖.X A) ∧ IsKleinFour (bar H W))) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H A : Set (Bar H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOKn : 𝔖.N₀ A ≤ normalizer (O (𝔖.N A) : Set G) :=
    G4c.N₀_le_N.trans (G4c.le_normalizer_O _)
  obtain ⟨hcovW, hfact, hnorm, hOeq, ⟨e⟩, hcent⟩ :=
    core f hker hOKn (G4c.odd_card_O _) hLodd hWH hWN hWn hWf
  have hXH : 𝔖.X A ≤ H := G4c.X_le_A.trans hAH
  have hYH : 𝔖.Y A ≤ H := G4c.Y_le_A.trans hAH
  refine ⟨le_inf hWH hWN, hXW, hcovW, hfact, hnorm, hOeq, ?_, hcent, ?_⟩
  · rcases hLt with hL | hL
    · exact Or.inl (isL2OrA7_of_mulEquiv e hL)
    · have hV : IsKleinFour (bar H W) := IsKleinFour.mk
        (by rw [Nat.card_congr e.toEquiv]; exact hL.card_four)
        (by rw [Monoid.exponent_eq_of_mulEquiv e]; exact hL.exponent_two)
      refine Or.inr ⟨?_, hV⟩
      have hX4 : Nat.card (𝔖.X A) = 4 := (G4b.isKleinFour_X 𝔖 hAS hA).card_four
      have hX2 : IsPGroup 2 (𝔖.X A) := IsPGroup.of_card (n := 2) (by rw [hX4]; norm_num)
      have hXb : Nat.card (bar H (𝔖.X A)) = 4 := by rw [card_bar hXH hX2, hX4]
      exact (eq_of_le_of_card_ge (G4c.bar_mono hXW) (by rw [hV.card_four, hXb])).symm
  · exact bar_inf_le_centralizer_of_sup (𝔖.decomp.e16_split hAS hA).1 hXW hXH hYH
      (G4c.O_le _) hcent

theorem X_eq_S₁_of_isKleinFour (hAS : A ≤ 𝔖.S) (hA : IsE16 A) {L : Type} [Group L]
    (f : 𝔖.N₀ A →* L) (hker : f.ker = (O (𝔖.N A)).subgroupOf (𝔖.N₀ A))
    (hS₁N : IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A)) (hL : IsKleinFour L) : 𝔖.X A = 𝔖.S₁ := by
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL.card_four]; norm_num)
  obtain ⟨P, -, hPc⟩ := exists_isPGroup_card_eq f hker (G4c.odd_card_O _) hS₁N.le
    (G4c.isPGroup_S₁ 𝔖)
  have h1 : Nat.card 𝔖.S₁ ≤ 4 := by
    rw [← hPc, ← hL.card_four]
    exact Subgroup.card_le_card_group P
  exact eq_of_le_of_card_ge G4c.X_le_S₁ (by rw [(G4b.isKleinFour_X 𝔖 hAS hA).card_four]; exact h1)

theorem eq_bot_of_odd_of_quot_N₀ {L : Type} [Group L] (f : 𝔖.N₀ A →* L)
    (hf : Function.Surjective f) (hker : f.ker = (O (𝔖.N A)).subgroupOf (𝔖.N₀ A))
    (hLt : IsL2OrA7 L 5 ∨ IsKleinFour L) (hS₁N : IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A)) :
    ∀ N : Subgroup L, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite L := Finite.of_surjective f hf
  rcases hLt with hL | hL
  · have := G4c.isSimpleGroup_of_isL2OrA7' le_rfl hL
    obtain ⟨P, hP, hPc⟩ := exists_isPGroup_card_eq f hker (G4c.odd_card_O _) hS₁N.le
      (G4c.isPGroup_S₁ 𝔖)
    refine eq_bot_of_normal_of_odd hP fun h => ?_
    have := 𝔖.four_le_card_S₁
    rw [← hPc, h, card_bot] at this
    omega
  · intro N _ hN
    refine Subgroup.eq_bot_of_card_eq N ?_
    have h4 : Nat.card N ∣ 4 := hL.card_four ▸ Subgroup.card_subgroup_dvd_card N
    have hle : Nat.card N ≤ 4 := Nat.le_of_dvd (by norm_num) h4
    obtain ⟨k, hk⟩ := hN
    interval_cases h : Nat.card N <;> omega

theorem exists_W_N_nonisolated (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (h44 : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
      CFSG.ABGLocalTools.IsSylowOf 2 ((𝔖.S₁ ⊓ J) ⊔ (𝔖.S₂ ⊓ J)) J →
      ∃ L₁ L₂ : Subgroup (Bar H), L₁ ≤ bar H J ∧ L₂ ≤ bar H J ∧ L₁ ⊓ L₂ = ⊥ ∧
        L₂ ≤ centralizer (L₁ : Set (Bar H)) ∧ ((L₁ ⊔ L₂).subgroupOf (bar H J)).Normal ∧
        bar H J = (L₁ ⊔ L₂) ⊔ (bar H J ⊓ normalizer (bar H A : Set (Bar H))) ∧
        IsL2PGL2OrA7OrV4 L₁ ∧ IsL2PGL2OrA7OrV4 L₂ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₁ ⊓ L₁) L₁ ∧
        CFSG.ABGLocalTools.IsSylowOf 2 (bar H 𝔖.S₂ ⊓ L₂) L₂ ∧
        bar H 𝔖.S₁ ⊓ bar H J ≤ L₁ ∧ bar H 𝔖.S₂ ⊓ bar H J ≤ L₂ ∧
        (L₁.subgroupOf (bar H J)).Normal ∧ (L₂.subgroupOf (bar H J)).Normal)
    {L : Type} [Group L] (f : 𝔖.N₀ A →* L) (hf : Function.Surjective f)
    (hker : f.ker = (O (𝔖.N A)).subgroupOf (𝔖.N₀ A)) (hLt : IsL2OrA7 L 5 ∨ IsKleinFour L)
    (hS₁N : IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A)) {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H)
    (hcov : Covers H (𝔖.N₀ A) (O (𝔖.N A)))
    (hsyl : IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) (hS₁H : 𝔖.S₁ ≤ H)
    (hiso : ∀ t, ¬ IsIsolatedIn H t) :
    ∃ W : Subgroup G, (W ≤ H ∧ W ≤ 𝔖.N₀ A ∧ 𝔖.X A ≤ W ∧ (bar H W).Normal ∧
      (W.subgroupOf (𝔖.N₀ A)).map f = ⊤) ∧
    ∃ L₂ : Subgroup (Bar H), L₂.Normal ∧ bar H (𝔖.Y A) ≤ L₂ ∧ L₂ ⊓ bar H W = ⊥ ∧
      L₂ ≤ centralizer (bar H W : Set (Bar H)) ∧ (IsL2PGL2OrA7OrV4 L₂ ∨ IsPGroup 2 L₂) ∧
      L₂ ⊔ bar H W ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOKodd : Odd (Nat.card (O (𝔖.N A))) := G4c.odd_card_O _
  have hOKn : 𝔖.N₀ A ≤ normalizer (O (𝔖.N A) : Set G) :=
    G4c.N₀_le_N.trans (G4c.le_normalizer_O _)
  have hS₁2 : IsPGroup 2 𝔖.S₁ := G4c.isPGroup_S₁ 𝔖
  have hS₁4 : 4 ≤ Nat.card 𝔖.S₁ := 𝔖.four_le_card_S₁
  have hS₁1 : 𝔖.S₁ ≠ ⊥ := fun h => by
    rw [h, card_bot] at hS₁4
    omega
  have hXH : 𝔖.X A ≤ H := G4c.X_le_A.trans hAH
  have hYH : 𝔖.Y A ≤ H := G4c.Y_le_A.trans hAH
  obtain ⟨L₁, L₂, -, -, hinf, hcent, -, hJeq, -, hL₂t, hS₁L₁, -, hT₁L₁, hT₂L₂, hn₁, hn₂⟩ :=
    h44 H hH hiso A hAH hA H (sup_le (G4c.O2_le H) hAH) le_rfl
      (isSylowOf_sup_inf 𝔖 hsyl (Or.inl hS₁H))
  rw [bar_self] at hJeq hT₁L₁ hT₂L₂ hn₁ hn₂
  rw [inf_top_eq] at hT₁L₁ hT₂L₂
  rw [top_inf_eq] at hJeq
  have hnorm : ∀ L' : Subgroup (Bar H), (L'.subgroupOf ⊤).Normal → L'.Normal := fun L' h =>
    G4c.normal_of_top_le_normalizer ((normal_subgroupOf_iff_le_normalizer le_top).mp h)
  have hL₁n := hnorm L₁ hn₁
  have hTL : IsSylowOf 2 (bar H 𝔖.S₁) L₁ := by
    rwa [inf_eq_left.mpr hT₁L₁] at hS₁L₁
  have hYL₂ : bar H (𝔖.Y A) ≤ L₂ := (G4c.bar_mono G4c.Y_le_S₂).trans hT₂L₂
  have hL₁C : L₁ ≤ centralizer (L₂ : Set (Bar H)) := le_centralizer_iff.mp hcent
  have hL₁Y : L₁ ≤ centralizer (bar H (𝔖.Y A) : Set (Bar H)) :=
    hL₁C.trans (centralizer_le hYL₂)
  have hAb : bar H A = bar H (𝔖.X A) ⊔ bar H (𝔖.Y A) := by
    rw [← G4c.bar_sup hXH hYH, G4b.X_sup_Y 𝔖 hAS hA]
  have hodd : ∀ x ∈ L₁ ⊓ normalizer (bar H 𝔖.S₁ : Set (Bar H)), Odd (orderOf x) →
      x ∈ normalizer (bar H A : Set (Bar H)) := by
    rcases 𝔖.decomp.dih₁.isKleinFour_or_isDihNonab with hV | hN
    · intro x hx _
      have hXS : 𝔖.X A = 𝔖.S₁ := eq_of_le_of_card_ge G4c.X_le_S₁
        (by rw [hV.card_four, (G4b.isKleinFour_X 𝔖 hAS hA).card_four])
      rw [hAb, hXS]
      exact mem_normalizer_sup (mem_inf.mp hx).2
        (centralizer_le_normalizer _ (hL₁Y (mem_inf.mp hx).1))
    · obtain ⟨k, hk, ⟨e⟩⟩ := hN
      obtain ⟨e'⟩ := nonempty_mulEquiv_bar hS₁H hS₁2
      refine mem_normalizer_of_odd (e'.symm.trans e) hk ?_ hL₁Y
      rw [hAb]
      exact sup_le ((G4c.bar_mono G4c.X_le_S₁).trans le_sup_right) le_sup_left
  have hTK : 𝔖.S₁ ≤ H ⊓ 𝔖.N₀ A := le_inf hS₁H hS₁N.le
  obtain ⟨-, hWn, hLW, hLWc, htopW⟩ := nonisolated (K₀ := 𝔖.N₀ A) hTK
    (hS₁N.of_le hTK inf_le_right) hYH ((G4c.isPGroup_S₂ 𝔖).to_le G4c.Y_le_S₂)
    (N_le_normalizer_N₀ 𝔖) hL₁n (by rwa [inf_comm]) hL₁C (by rw [hJeq, sup_comm L₁ L₂])
    hTL hYL₂ hodd
  have hWHN : genW H (𝔖.N₀ A) 𝔖.S₁ ≤ H ⊓ 𝔖.N₀ A := genW_le hTK
  refine ⟨genW H (𝔖.N₀ A) 𝔖.S₁, ⟨hWHN.trans inf_le_left, hWHN.trans inf_le_right,
    G4c.X_le_S₁.trans le_genW, hWn, ?_⟩, L₂, hnorm L₂ hn₂, hYL₂, hLW, hLWc, Or.inl hL₂t, htopW⟩
  rcases hLt with hL | hL
  · have := G4c.isSimpleGroup_of_isL2OrA7' le_rfl hL
    exact map_eq_top_of_isSimpleGroup f hf hker hOKodd hOKn hcov (hWHN.trans inf_le_right)
      le_normalizer_genW le_genW hS₁2 hS₁1
  · have h1 := map_eq_top_of_isPGroup f hf
      (IsPGroup.of_card (n := 2) (by rw [hL.card_four]; norm_num)) hS₁N
    rw [eq_top_iff, ← h1]
    exact map_mono (comap_mono le_genW)

theorem exists_W_N_isolated_Y (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
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
    {L : Type} [Group L] (f : 𝔖.N₀ A →* L) (hf : Function.Surjective f)
    (hker : f.ker = (O (𝔖.N A)).subgroupOf (𝔖.N₀ A))
    {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H (𝔖.N₀ A) (O (𝔖.N A)))
    {t : G} (ht : IsIsolatedIn H t) (htY : t ∈ 𝔖.Y A) :
    ((H ⊓ 𝔖.N₀ A) ≤ H ∧ (H ⊓ 𝔖.N₀ A) ≤ 𝔖.N₀ A ∧ 𝔖.X A ≤ H ⊓ 𝔖.N₀ A ∧
      (bar H (H ⊓ 𝔖.N₀ A)).Normal ∧ ((H ⊓ 𝔖.N₀ A).subgroupOf (𝔖.N₀ A)).map f = ⊤) ∧
    ∃ L₂ : Subgroup (Bar H), L₂.Normal ∧ bar H (𝔖.Y A) ≤ L₂ ∧ L₂ ⊓ bar H (H ⊓ 𝔖.N₀ A) = ⊥ ∧
      L₂ ≤ centralizer (bar H (H ⊓ 𝔖.N₀ A) : Set (Bar H)) ∧
      (IsL2PGL2OrA7OrV4 L₂ ∨ IsPGroup 2 L₂) ∧
      L₂ ⊔ bar H (H ⊓ 𝔖.N₀ A) ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOKn : 𝔖.N₀ A ≤ normalizer (O (𝔖.N A) : Set G) :=
    G4c.N₀_le_N.trans (G4c.le_normalizer_O _)
  have hS₁N : IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) := h48.2.1
  have hXN : 𝔖.X A ≤ 𝔖.N₀ A := G4c.X_le_S₁.trans hS₁N.le
  have hXH : 𝔖.X A ≤ H := G4c.X_le_A.trans hAH
  have htA : t ∈ A := G4c.Y_le_A htY
  have ht1 : t ≠ 1 := by
    rintro rfl
    have h := ht.2.1
    rw [orderOf_one] at h
    exact absurd h (by norm_num)
  have hNC : 𝔖.N A ≤ C t := G4c.N_le_C htY
  have htN : t ∈ 𝔖.N A := mem_centralizer_iff.mpr fun _ hy =>
    G4b.comm_of_isE16 hA (G4c.Y_le_A hy) htA
  have hcovN : Covers (𝔖.N A) (𝔖.N₀ A) (O (𝔖.N A)) := fun x hx =>
    mem_sup_left (mem_inf.mpr ⟨G4c.N₀_le_N hx, hx⟩)
  have hON : O (𝔖.N A) ≤ O (C t) :=
    le_trans (le_inf le_rfl ((G4c.O_le _).trans hNC))
      ((𝔖.lemma_4_13_of hA h315 h47 h48 (𝔖.N A) (N_ne_top 𝔖 hAS hA)).2 hcovN t htY ht1 htN)
  have h5 := h48.2.2.2.2.2 t htY ht1
  have hsupO : (H ⊓ 𝔖.N₀ A) ⊔ O (C t) = ⁅O2 (C t), O2 (C t)⁆ ⊔ O (C t) :=
    inf_sup_O_eq hNC hON h5 hcov
  have hWt : H ⊓ 𝔖.N₀ A ≤ H ⊓ C t := inf_le_inf_left _ (G4c.N₀_le_N.trans hNC)
  have hWn : (bar H (H ⊓ 𝔖.N₀ A)).Normal := by
    refine bar_normal_of_isIsolatedIn ht hWt ?_
    rw [hsupO]
    exact inf_le_right.trans (le_normalizer_commutator_sup_O (C t))
  have hWf : ((H ⊓ 𝔖.N₀ A).subgroupOf (𝔖.N₀ A)).map f = ⊤ := by
    rw [eq_top_iff]
    rintro l -
    obtain ⟨k, rfl⟩ := hf l
    obtain ⟨h, hhH, hhk⟩ := exists_map_eq_of_covers f hker hOKn hcov k
    exact ⟨h, mem_inf.mpr ⟨hhH, h.2⟩, hhk⟩
  refine ⟨⟨inf_le_left, inf_le_right, le_inf hXH hXN, hWn, hWf⟩, ?_⟩
  have hOt : O H ⊓ C t ≤ O (C t) :=
    (𝔖.lemma_4_13_of hA h315 h47 h48 H hH).2 hcov t htY ht1 ht.1
  obtain ⟨g, hg, hXg, hYg⟩ := G4c.exists_conj_align hA htA
    (𝔖.fusion.conj₂ t (G4c.Y_le_S₂ htY) 𝔖.z₂ 𝔖.hz₂.1 ht.2.1 𝔖.hz₂.2.1) (G4c.S_le_C_z₂ 𝔖)
  obtain ⟨-, ⟨K₁, hRF, hRF', hFR, hTL, -⟩⟩ := h315
  have hFK : ⁅K₁, K₁⁆ ≤ K₁ := G4c.commutator_le_of_le le_rfl le_rfl
  have hTK : IsSylowOf 2 (bar (C 𝔖.z₂) 𝔖.S₁) K₁ :=
    isSylowOf_bar_of_sup 𝔖.S ((G4c.S_eq 𝔖).trans (sup_comm _ _)) (G4c.S_le_C_z₂ 𝔖) hRF hRF' hFR
      (hTL.trans hFK)
  have hWF : bar (C 𝔖.z₂) ((H ⊓ 𝔖.N₀ A).map (G4c.cj g)) = ⁅K₁, K₁⁆ :=
    (bar_map_inf_eq hg hNC hON h5 hcov).trans
      (G4c.bar_commutator_O2_eq 𝔖.S ((G4c.S_eq 𝔖).trans (sup_comm _ _)) (G4c.S_le_C_z₂ 𝔖)
        (G4c.isPGroup_S₂ 𝔖) hRF hRF' hFR hTL)
  have hAt : A ≤ H ⊓ C t := le_inf hAH fun _ ha =>
    mem_centralizer_singleton_iff.mpr (G4b.comm_of_isE16 hA ha htA)
  have hS₂z : 𝔖.S₂ ≤ C 𝔖.z₂ := 𝔖.hz₂.2.2
  have hAg : bar (C 𝔖.z₂) (A.map (G4c.cj g)) ≤
      bar (C 𝔖.z₂) 𝔖.S₂ ⊔ bar (C 𝔖.z₂) 𝔖.S₁ := by
    rw [← G4b.X_sup_Y 𝔖 hAS hA, G4c.map_cj_sup, sup_comm (bar (C 𝔖.z₂) 𝔖.S₂)]
    exact (G4c.bar_mono (sup_le_sup hXg hYg)).trans
      (G4c.bar_sup (G4c.S₁_le_C_z₂ 𝔖) hS₂z).le
  have hodd : ∀ x ∈ K₁ ⊓ normalizer (bar (C 𝔖.z₂) 𝔖.S₁ : Set (Bar (C 𝔖.z₂))),
      Odd (orderOf x) →
      x ∈ normalizer (bar (C 𝔖.z₂) (A.map (G4c.cj g)) : Set (Bar (C 𝔖.z₂))) := by
    rcases 𝔖.decomp.dih₁.isKleinFour_or_isDihNonab with hV | hN
    ·
      intro x hx _
      have hXS : 𝔖.X A = 𝔖.S₁ := eq_of_le_of_card_ge G4c.X_le_S₁
        (by rw [hV.card_four, (G4b.isKleinFour_X 𝔖 hAS hA).card_four])
      have hXg' : (𝔖.X A).map (G4c.cj g) = 𝔖.S₁ :=
        eq_of_le_of_card_ge hXg (by rw [G4c.card_map_cj, hXS])
      have hYgC : (𝔖.Y A).map (G4c.cj g) ≤ C 𝔖.z₂ := hYg.trans hS₂z
      rw [← G4b.X_sup_Y 𝔖 hAS hA, G4c.map_cj_sup, G4c.bar_sup (hXg'.le.trans (G4c.S₁_le_C_z₂ 𝔖))
        hYgC, hXg']
      exact mem_normalizer_sup (mem_inf.mp hx).2 (centralizer_le_normalizer _
        ((hFR.trans (centralizer_le (G4c.bar_mono hYg))) (mem_inf.mp hx).1))
    · obtain ⟨k, hk, ⟨e⟩⟩ := hN
      obtain ⟨e'⟩ := nonempty_mulEquiv_bar (G4c.S₁_le_C_z₂ 𝔖) (G4c.isPGroup_S₁ 𝔖)
      exact mem_normalizer_of_odd (e'.symm.trans e) hk hAg hFR
  obtain ⟨L₂, hL₂n, hYL, hLW, hLWc, hL2, htop, -⟩ :=
    exists_L_of_isIsolatedIn ht hOt hg hRF hRF' hFR (isPGroup_bar (G4c.isPGroup_S₂ 𝔖))
      hTL hTK (G4c.N₀_le_N.trans hNC) hWF hAt G4c.Y_le_A (G4c.bar_mono hYg) hodd
  exact ⟨L₂, hL₂n, hYL, hLW, hLWc, Or.inr hL2, htop⟩

theorem exists_W_N_isolated_X (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (h315 : (∃ H₁ : Subgroup (Bar (C 𝔖.z₁)), bar (C 𝔖.z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧
        bar (C 𝔖.z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧ H₁ ≤ centralizer (bar (C 𝔖.z₁) 𝔖.S₁ : Set (Bar (C 𝔖.z₁))) ∧
        bar (C 𝔖.z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C 𝔖.z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C 𝔖.z₂)), bar (C 𝔖.z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧
        bar (C 𝔖.z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧ K₁ ≤ centralizer (bar (C 𝔖.z₂) 𝔖.S₂ : Set (Bar (C 𝔖.z₂))) ∧
        bar (C 𝔖.z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C 𝔖.z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C 𝔖.z₂) 𝔖.S₁)))
    {L : Type} [Group L] (f : 𝔖.N₀ A →* L) (hf : Function.Surjective f)
    (hker : f.ker = (O (𝔖.N A)).subgroupOf (𝔖.N₀ A)) (hLt : IsL2OrA7 L 5 ∨ IsKleinFour L)
    (hS₁N : IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A)) {H : Subgroup G} (hAH : A ≤ H)
    (hcov : Covers H (𝔖.N₀ A) (O (𝔖.N A))) {t : G} (ht : IsIsolatedIn H t) (htX : t ∈ 𝔖.X A) :
    IsKleinFour L ∧ 𝔖.X A ≤ H ∧ 𝔖.X A ≤ 𝔖.N₀ A ∧ (bar H (𝔖.X A)).Normal ∧
      ((𝔖.X A).subgroupOf (𝔖.N₀ A)).map f = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOKn : 𝔖.N₀ A ≤ normalizer (O (𝔖.N A) : Set G) :=
    G4c.N₀_le_N.trans (G4c.le_normalizer_O _)
  have hS₁2 : IsPGroup 2 𝔖.S₁ := G4c.isPGroup_S₁ 𝔖
  have hXN : 𝔖.X A ≤ 𝔖.N₀ A := G4c.X_le_S₁.trans hS₁N.le
  have hXH : 𝔖.X A ≤ H := G4c.X_le_A.trans hAH
  have htA : t ∈ A := G4c.X_le_A htX
  have hL : IsKleinFour L := by
    rcases hLt with hL | hL
    · have := G4c.isSimpleGroup_of_isL2OrA7' le_rfl hL
      exact (false_of_isIsolatedIn_mem f hf hker (G4c.odd_card_O _) hOKn hcov hS₁N.le hS₁2
        𝔖.four_le_card_S₁ ht (hXN htX)).elim
    · exact hL
  have hXS := X_eq_S₁_of_isKleinFour 𝔖 hAS hA f hker hS₁N hL
  obtain ⟨g, hg, hXg, -⟩ := G4c.exists_conj_align hA htA
    (𝔖.fusion.conj₁ t (G4c.X_le_S₁ htX) 𝔖.z₁ 𝔖.hz₁.1 ht.2.1 𝔖.hz₁.2.1) (G4c.S_le_C_z₁ 𝔖)
  have hXg' : (𝔖.X A).map (G4c.cj g) = 𝔖.S₁ :=
    eq_of_le_of_card_ge hXg (by rw [G4c.card_map_cj, hXS])
  obtain ⟨⟨H₁, -, hRF₁', hFR₁, -, -⟩, -⟩ := h315
  have hXt : 𝔖.X A ≤ C t := G4c.X_le_A.trans fun _ ha =>
    mem_centralizer_singleton_iff.mpr (G4b.comm_of_isE16 hA ha htA)
  have hKn : H ⊓ C t ≤ normalizer ((𝔖.X A ⊔ O (C t) : Subgroup G) : Set G) :=
    inf_le_right.trans (le_normalizer_sup_O_of_conj hg hXt
      (by rw [hXg']; exact G4c.bar_normal_of_sup hRF₁' hFR₁))
  refine ⟨hL, hXH, hXN, bar_normal_of_isIsolatedIn ht (le_inf hXH hXt) hKn, ?_⟩
  rw [hXS]
  exact map_eq_top_of_isPGroup f hf (IsPGroup.of_card (n := 2) (by rw [hL.card_four]; norm_num))
    hS₁N

theorem exists_W_N_isolated_XY (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (h317 : HasNormalTwoComplement (C (𝔖.z₁ * 𝔖.z₂)))
    {L : Type} [Group L] (f : 𝔖.N₀ A →* L) (hf : Function.Surjective f)
    (hker : f.ker = (O (𝔖.N A)).subgroupOf (𝔖.N₀ A)) (hLt : IsL2OrA7 L 5 ∨ IsKleinFour L)
    (hS₁N : IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A)) {H : Subgroup G} (hAH : A ≤ H)
    (hcov : Covers H (𝔖.N₀ A) (O (𝔖.N A)))
    (hsyl : IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) {t : G} (ht : IsIsolatedIn H t)
    (htA : t ∈ A) (htX : t ∉ 𝔖.X A) (htY : t ∉ 𝔖.Y A) :
    𝔖.X A ≤ H ∧ 𝔖.X A ≤ 𝔖.N₀ A ∧ (bar H (𝔖.X A)).Normal ∧
      ((𝔖.X A).subgroupOf (𝔖.N₀ A)).map f = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOKn : 𝔖.N₀ A ≤ normalizer (O (𝔖.N A) : Set G) :=
    G4c.N₀_le_N.trans (G4c.le_normalizer_O _)
  have hS₁2 : IsPGroup 2 𝔖.S₁ := G4c.isPGroup_S₁ 𝔖
  have hH2 : IsPGroup 2 (Bar H) := isPGroup_bar_of_isIsolatedIn 𝔖 hAS hA h317 ht htA htX htY
  have hL : IsKleinFour L := by
    rcases hLt with hL | hL
    · have := G4c.isSimpleGroup_of_isL2OrA7' le_rfl hL
      exact (false_of_isPGroup_bar f hf hker (G4c.odd_card_O _) hOKn hcov hS₁N.le hS₁2
        𝔖.four_le_card_S₁ hH2).elim
    · exact hL
  have hXS := X_eq_S₁_of_isKleinFour 𝔖 hAS hA f hker hS₁N hL
  have hSb : bar H ((𝔖.S : Subgroup G) ⊓ H) = ⊤ := by
    have h1 : IsSylowOf 2 (bar H ((𝔖.S : Subgroup G) ⊓ H)) (bar H H) := isSylowOf_bar le_rfl hsyl
    rw [bar_self] at h1
    exact (h1.eq_of_le le_top le_rfl (hH2.to_subgroup ⊤)).symm
  have hSN : (𝔖.S : Subgroup G) ≤ normalizer (𝔖.S₁ : Set G) := by
    rw [G4c.S_eq 𝔖]
    exact sup_le le_normalizer (CFSG.CGT.Foote81L6.le_normalizer_of_comm fun x hx y hy =>
      𝔖.decomp.comm hx hy)
  refine ⟨G4c.X_le_A.trans hAH, G4c.X_le_S₁.trans hS₁N.le, ?_, ?_⟩
  · refine G4c.normal_of_top_le_normalizer ?_
    rw [← hSb]
    rintro _ ⟨⟨s, hsH⟩, hs, rfl⟩
    have hsS : s ∈ (𝔖.S : Subgroup G) := (mem_inf.mp hs).1
    refine G4c.mem_normalizer_of_map_cj_eq ?_
    rw [← bar_map_cj (𝔖.X A) hsH, hXS, G4c.map_cj_eq_of_mem_normalizer (hSN hsS)]
  · rw [hXS]
    exact map_eq_top_of_isPGroup f hf
      (IsPGroup.of_card (n := 2) (by rw [hL.card_four]; norm_num)) hS₁N

variable {𝔖}

theorem sec5_one_N_of_isSylowOf (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (h44 : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
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
    (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H (𝔖.N₀ A) (O (𝔖.N A)))
    (hsyl : IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) :
    ∃ W : Subgroup G, W ≤ H ⊓ 𝔖.N₀ A ∧ 𝔖.X A ≤ W ∧ Covers W (𝔖.N₀ A) (O (𝔖.N A)) ∧
      H ⊓ 𝔖.N₀ A ≤ W ⊔ (H ⊓ O (𝔖.N A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
      O H ⊓ W = W ⊓ O (𝔖.N A) ∧
      (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H (𝔖.X A) ∧ IsKleinFour (bar H W))) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H A : Set (Bar H)) := by
  obtain ⟨L, _, f, hf, hker, hLt⟩ := h48.1
  have hS₁N : IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) := h48.2.1
  have hLodd := eq_bot_of_odd_of_quot_N₀ 𝔖 f hf hker hLt hS₁N
  have hS₁H : 𝔖.S₁ ≤ H := le_of_covers 𝔖 (Or.inl rfl) hS₁N (G4c.odd_card_O _)
    (G4c.N₀_le_N.trans (G4c.le_normalizer_O _)) hcov hsyl
  obtain ⟨W, hWH, hWN, hXW, hWn, hWf⟩ : ∃ W : Subgroup G, W ≤ H ∧ W ≤ 𝔖.N₀ A ∧ 𝔖.X A ≤ W ∧
      (bar H W).Normal ∧ (W.subgroupOf (𝔖.N₀ A)).map f = ⊤ := by
    by_cases hiso : ∃ t, IsIsolatedIn H t
    · obtain ⟨t₀, ht₀⟩ := hiso
      obtain ⟨t, htA, ht⟩ := exists_isIsolatedIn_mem_A 𝔖 hAS hA hAH hsyl ht₀
      by_cases htY : t ∈ 𝔖.Y A
      · exact ⟨_, (exists_W_N_isolated_Y 𝔖 hAS hA h315 h47 h48 f hf hker hH hAH hcov ht
          htY).1⟩
      by_cases htX : t ∈ 𝔖.X A
      · obtain ⟨-, h⟩ := exists_W_N_isolated_X 𝔖 hAS hA h315 f hf hker hLt hS₁N hAH hcov ht htX
        exact ⟨_, h.1, h.2.1, le_rfl, h.2.2⟩
      · obtain h := exists_W_N_isolated_XY 𝔖 hAS hA h317 f hf hker hLt hS₁N hAH hcov hsyl ht
          htA htX htY
        exact ⟨_, h.1, h.2.1, le_rfl, h.2.2⟩
    · obtain ⟨W, hW, -⟩ := exists_W_N_nonisolated 𝔖 hAS hA h44 f hf hker hLt hS₁N hH hAH hcov
        hsyl hS₁H fun t ht => hiso ⟨t, ht⟩
      exact ⟨W, hW⟩
  exact ⟨W, sec5_one_N_of_W 𝔖 hAS hA f hker hLt hLodd hAH hWH hWN hXW hWn hWf⟩

theorem sec5_one_N_of (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (h44 : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
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
    (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H (𝔖.N₀ A) (O (𝔖.N A))) :
    ∃ W : Subgroup G, W ≤ H ⊓ 𝔖.N₀ A ∧ 𝔖.X A ≤ W ∧ Covers W (𝔖.N₀ A) (O (𝔖.N A)) ∧
      H ⊓ 𝔖.N₀ A ≤ W ⊔ (H ⊓ O (𝔖.N A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
      O H ⊓ W = W ⊓ O (𝔖.N A) ∧
      (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H (𝔖.X A) ∧ IsKleinFour (bar H W))) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H A : Set (Bar H)) := by
  obtain ⟨n, hn, hsyl⟩ := exists_conj_isSylowOf 𝔖 hAS hA hAH
  have hAn : A.map (G4c.cj n) = A := G4c.map_cj_eq_of_mem_normalizer hn
  have hN₀n : (𝔖.N₀ A).map (G4c.cj n) = 𝔖.N₀ A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_N₀ 𝔖 hAS hA hn)
  have hONn : (O (𝔖.N A)).map (G4c.cj n) = O (𝔖.N A) := by
    rw [G4c.map_cj_O, G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_N 𝔖 hAS hA hn)]
  have hH' : H.map (G4c.cj n) ≠ ⊤ := by
    intro h
    apply hH
    rw [← G4c.map_cj_cj_inv n H, h]
    exact map_top_of_surjective _ (MulAut.conj n⁻¹).surjective
  have hAH' : A ≤ H.map (G4c.cj n) := hAn ▸ map_mono hAH
  have hcov' : Covers (H.map (G4c.cj n)) (𝔖.N₀ A) (O (𝔖.N A)) := by
    have := G5d.covers_map_conj hcov n
    rwa [hN₀n, hONn] at this
  obtain ⟨W', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    sec5_one_N_of_isSylowOf hAS hA h44 h315 h317 h47 h48 _ hH' hAH' hcov' hsyl
  have hn' : n⁻¹ ∈ normalizer (A : Set G) := inv_mem hn
  have hHH : (H.map (G4c.cj n)).map (G4c.cj n⁻¹) = H := G4c.map_cj_cj_inv n H
  have hA' : A.map (G4c.cj n⁻¹) = A := G4c.map_cj_eq_of_mem_normalizer hn'
  have hN₀' : (𝔖.N₀ A).map (G4c.cj n⁻¹) = 𝔖.N₀ A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_N₀ 𝔖 hAS hA hn')
  have hON' : (O (𝔖.N A)).map (G4c.cj n⁻¹) = O (𝔖.N A) := by
    rw [G4c.map_cj_O,
      G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_N 𝔖 hAS hA hn')]
  have hX' : (𝔖.X A).map (G4c.cj n⁻¹) = 𝔖.X A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_X 𝔖 hAS hA hn')
  obtain ⟨ψ, hψ, t1, t2, t3, t4, t5, t6, t7, t8⟩ :=
    transport_W hHH hN₀' hON' hX' hA' ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩
  obtain ⟨eW⟩ := nonempty_bar_mulEquiv_of_transport (W := W') ψ hψ
  refine ⟨W'.map (G4c.cj n⁻¹), t1, t2, t3, t4, t5, t6, ?_, t7, t8⟩
  rcases h7 with h7 | ⟨h7, h7'⟩
  · exact Or.inl (isL2OrA7_of_mulEquiv eW h7)
  · refine Or.inr ⟨?_, IsKleinFour.mk (by rw [Nat.card_congr eW.toEquiv]; exact h7'.card_four)
      (by rw [Monoid.exponent_eq_of_mulEquiv eW]; exact h7'.exponent_two)⟩
    rw [← hψ W', ← hX', ← hψ (𝔖.X A), h7]

theorem sec5_one_N_L₂_of_isSylowOf (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (h44 : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
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
    (hns : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5))
    (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H (𝔖.N₀ A) (O (𝔖.N A)))
    (hsyl : IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) :
    ∃ W : Subgroup G, ∃ L₂ : Subgroup (Bar H), W ≤ H ⊓ 𝔖.N₀ A ∧ 𝔖.X A ≤ W ∧
      Covers W (𝔖.N₀ A) (O (𝔖.N A)) ∧ H ⊓ 𝔖.N₀ A ≤ W ⊔ (H ⊓ O (𝔖.N A)) ∧
      ((W ⊔ O H).subgroupOf H).Normal ∧ O H ⊓ W = W ⊓ O (𝔖.N A) ∧
      (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H (𝔖.X A) ∧ IsKleinFour (bar H W))) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H A : Set (Bar H)) ∧
      L₂.Normal ∧ bar H (𝔖.Y A) ≤ L₂ ∧ L₂ ⊓ bar H W = ⊥ ∧
      L₂ ≤ centralizer (bar H W : Set (Bar H)) ∧ (IsL2PGL2OrA7OrV4 L₂ ∨ IsPGroup 2 L₂) ∧
      L₂ ⊔ bar H W ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ := by
  obtain ⟨L, _, f, hf, hker, hL5⟩ := hns
  have hLt : IsL2OrA7 L 5 ∨ IsKleinFour L := Or.inl hL5
  have hS₁N : IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) := h48.2.1
  have hLodd := eq_bot_of_odd_of_quot_N₀ 𝔖 f hf hker hLt hS₁N
  have hOKn : 𝔖.N₀ A ≤ normalizer (O (𝔖.N A) : Set G) :=
    G4c.N₀_le_N.trans (G4c.le_normalizer_O _)
  have hS₁H : 𝔖.S₁ ≤ H := le_of_covers 𝔖 (Or.inl rfl) hS₁N (G4c.odd_card_O _) hOKn hcov hsyl
  by_cases hiso : ∃ t, IsIsolatedIn H t
  · obtain ⟨t₀, ht₀⟩ := hiso
    obtain ⟨t, htA, ht⟩ := exists_isIsolatedIn_mem_A 𝔖 hAS hA hAH hsyl ht₀
    by_cases htY : t ∈ 𝔖.Y A
    · obtain ⟨⟨hWH, hWN, hXW, hWn, hWf⟩, L₂, hL₂⟩ :=
        exists_W_N_isolated_Y 𝔖 hAS hA h315 h47 h48 f hf hker hH hAH hcov ht htY
      obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ :=
        sec5_one_N_of_W 𝔖 hAS hA f hker hLt hLodd hAH hWH hWN hXW hWn hWf
      exact ⟨_, L₂, w1, w2, w3, w4, w5, w6, w7, w8, w9, hL₂⟩
    exfalso
    have := G4c.isSimpleGroup_of_isL2OrA7' le_rfl hL5
    by_cases htX : t ∈ 𝔖.X A
    · exact false_of_isIsolatedIn_mem f hf hker (G4c.odd_card_O _) hOKn hcov hS₁N.le
        (G4c.isPGroup_S₁ 𝔖) 𝔖.four_le_card_S₁ ht (hS₁N.le (G4c.X_le_S₁ htX))
    · exact false_of_isPGroup_bar f hf hker (G4c.odd_card_O _) hOKn hcov hS₁N.le
        (G4c.isPGroup_S₁ 𝔖) 𝔖.four_le_card_S₁
        (isPGroup_bar_of_isIsolatedIn 𝔖 hAS hA h317 ht htA htX htY)
  · obtain ⟨W, ⟨hWH, hWN, hXW, hWn, hWf⟩, L₂, hL₂⟩ := exists_W_N_nonisolated 𝔖 hAS hA h44 f hf
      hker hLt hS₁N hH hAH hcov hsyl hS₁H fun t ht => hiso ⟨t, ht⟩
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ :=
      sec5_one_N_of_W 𝔖 hAS hA f hker hLt hLodd hAH hWH hWN hXW hWn hWf
    exact ⟨W, L₂, w1, w2, w3, w4, w5, w6, w7, w8, w9, hL₂⟩

theorem sec5_one_N_L₂_of (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (h44 : ∀ H : Subgroup G, H ≠ ⊤ → (∀ t, ¬ IsIsolatedIn H t) →
      ∀ A : Subgroup G, A ≤ H → IsE16 A → ∀ J : Subgroup G, O2 H ⊔ A ≤ J → J ≤ H →
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
    (hns : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5))
    (H : Subgroup G) (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H (𝔖.N₀ A) (O (𝔖.N A))) :
    ∃ W : Subgroup G, ∃ L₂ : Subgroup (Bar H), W ≤ H ⊓ 𝔖.N₀ A ∧ 𝔖.X A ≤ W ∧
      Covers W (𝔖.N₀ A) (O (𝔖.N A)) ∧ H ⊓ 𝔖.N₀ A ≤ W ⊔ (H ⊓ O (𝔖.N A)) ∧
      ((W ⊔ O H).subgroupOf H).Normal ∧ O H ⊓ W = W ⊓ O (𝔖.N A) ∧
      (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H (𝔖.X A) ∧ IsKleinFour (bar H W))) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
      bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H A : Set (Bar H)) ∧
      L₂.Normal ∧ bar H (𝔖.Y A) ≤ L₂ ∧ L₂ ⊓ bar H W = ⊥ ∧
      L₂ ≤ centralizer (bar H W : Set (Bar H)) ∧ (IsL2PGL2OrA7OrV4 L₂ ∨ IsPGroup 2 L₂) ∧
      L₂ ⊔ bar H W ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ := by
  obtain ⟨n, hn, hsyl⟩ := exists_conj_isSylowOf 𝔖 hAS hA hAH
  have hAn : A.map (G4c.cj n) = A := G4c.map_cj_eq_of_mem_normalizer hn
  have hN₀n : (𝔖.N₀ A).map (G4c.cj n) = 𝔖.N₀ A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_N₀ 𝔖 hAS hA hn)
  have hONn : (O (𝔖.N A)).map (G4c.cj n) = O (𝔖.N A) := by
    rw [G4c.map_cj_O, G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_N 𝔖 hAS hA hn)]
  have hH' : H.map (G4c.cj n) ≠ ⊤ := by
    intro h
    apply hH
    rw [← G4c.map_cj_cj_inv n H, h]
    exact map_top_of_surjective _ (MulAut.conj n⁻¹).surjective
  have hAH' : A ≤ H.map (G4c.cj n) := hAn ▸ map_mono hAH
  have hcov' : Covers (H.map (G4c.cj n)) (𝔖.N₀ A) (O (𝔖.N A)) := by
    have := G5d.covers_map_conj hcov n
    rwa [hN₀n, hONn] at this
  obtain ⟨W', L₂', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    sec5_one_N_L₂_of_isSylowOf hAS hA h44 h315 h317 h47 h48 hns _ hH' hAH' hcov' hsyl
  have hn' : n⁻¹ ∈ normalizer (A : Set G) := inv_mem hn
  have hHH : (H.map (G4c.cj n)).map (G4c.cj n⁻¹) = H := G4c.map_cj_cj_inv n H
  have hA' : A.map (G4c.cj n⁻¹) = A := G4c.map_cj_eq_of_mem_normalizer hn'
  have hN₀' : (𝔖.N₀ A).map (G4c.cj n⁻¹) = 𝔖.N₀ A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_N₀ 𝔖 hAS hA hn')
  have hON' : (O (𝔖.N A)).map (G4c.cj n⁻¹) = O (𝔖.N A) := by
    rw [G4c.map_cj_O,
      G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_N 𝔖 hAS hA hn')]
  have hX' : (𝔖.X A).map (G4c.cj n⁻¹) = 𝔖.X A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_X 𝔖 hAS hA hn')
  have hY' : (𝔖.Y A).map (G4c.cj n⁻¹) = 𝔖.Y A :=
    G4c.map_cj_eq_of_mem_normalizer (G4b.normalizer_le_normalizer_Y 𝔖 hAS hA hn')
  obtain ⟨ψ, hψ, t1, t2, t3, t4, t5, t6, t7, t8⟩ :=
    transport_W hHH hN₀' hON' hX' hA' ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩
  obtain ⟨L₂, l1, l2, l3, l4, l5, l6⟩ :=
    transport_L ψ hψ hY' hA' ⟨h10, h11, h12, h13, h14, h15⟩
  obtain ⟨eW⟩ := nonempty_bar_mulEquiv_of_transport (W := W') ψ hψ
  refine ⟨W'.map (G4c.cj n⁻¹), L₂, t1, t2, t3, t4, t5, t6, ?_, t7, t8, l1, l2, l3, l4, l5, l6⟩
  rcases h7 with h7 | ⟨h7, h7'⟩
  · exact Or.inl (isL2OrA7_of_mulEquiv eW h7)
  · refine Or.inr ⟨?_, IsKleinFour.mk (by rw [Nat.card_congr eW.toEquiv]; exact h7'.card_four)
      (by rw [Monoid.exponent_eq_of_mulEquiv eW]; exact h7'.exponent_two)⟩
    rw [← hψ W', ← hX', ← hψ (𝔖.X A), h7]

end Sec4Setting

end CFSG.GH72
