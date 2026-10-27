module

public import CFSG.GH74.GLS.C3.Layer1.Th2Leaves
public import CFSG.GH74.E2.ComponentsBasic

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_A7_notC2 : Prop := ¬ InC2 ↥(alternatingGroup (Fin 7))

@[expose] def B_thm2_v2star_ss : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    (∃ (x y : G) (K : Subgroup G), IsV2StarTriple x y K) →
      ∃ (x y : G) (K : Subgroup G), IsV2StarStar x y K

section Max

variable {G : Type} [Group G]

open Classical in
noncomputable def Th2.aVal (K : Subgroup G) : ℕ :=
  if Nonempty (kBar K ≃* alternatingGroup (Fin 7)) then 2 else if InC2 (kBar K) then 0 else 1

noncomputable def Th2.muVal (K : Subgroup G) : ℕ :=
  Th2.aVal K * (Nat.card G + 1) + Nat.card (kBar K)

theorem Th2.aVal_of_A7 {K : Subgroup G} (h : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) :
    Th2.aVal K = 2 := by
  classical
  unfold Th2.aVal
  simp [h]

theorem Th2.aVal_of_C2 {K : Subgroup G} (hc : InC2 (kBar K))
    (hn : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) : Th2.aVal K = 0 := by
  classical
  unfold Th2.aVal
  simp [hn, hc]

theorem Th2.aVal_of_other {K : Subgroup G} (hc : ¬ InC2 (kBar K))
    (hn : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) : Th2.aVal K = 1 := by
  classical
  unfold Th2.aVal
  simp [hn, hc]

theorem Th2.card_kBar_lt [Finite G] (K : Subgroup G) : Nat.card (kBar K) < Nat.card G + 1 := by
  have h1 : Nat.card (kBar K) ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' (pPrimeCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card ↥K ≤ Nat.card G := Subgroup.card_le_card_group K
  omega

theorem Th2.muVal_lt_of_u2Succ [Finite G] (hA7 : B_A7_notC2) {K K' : Subgroup G}
    (h : U2Succ (kBar K') (kBar K)) : Th2.muVal K < Th2.muVal K' := by
  have hA7' : ∀ (H : Type) [Group H], InC2 H → ¬ Nonempty (H ≃* alternatingGroup (Fin 7)) :=
    fun H _ hc ⟨e⟩ => hA7 (CFSG.GH74.E2.inC2_of_mulEquiv e hc)
  have hK := Th2.card_kBar_lt K
  obtain ⟨-, -, hcases⟩ := h
  unfold Th2.muVal
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hboth, hlt⟩
  · rw [Th2.aVal_of_A7 h1]
    have : Th2.aVal K ≤ 1 := by
      by_cases hc : InC2 (kBar K)
      · rw [Th2.aVal_of_C2 hc h2]; omega
      · rw [Th2.aVal_of_other hc h2]
    nlinarith
  · have hJ := Th2.aVal_of_C2 h2 (hA7' _ h2)
    have hH : 1 ≤ Th2.aVal K' := by
      by_cases hn : Nonempty (kBar K' ≃* alternatingGroup (Fin 7))
      · rw [Th2.aVal_of_A7 hn]; omega
      · rw [Th2.aVal_of_other h1 hn]
    rw [hJ]
    nlinarith
  · rcases hboth with ⟨hc1, hc2⟩ | ⟨⟨hc1, hn1⟩, ⟨hc2, hn2⟩⟩
    · rw [Th2.aVal_of_C2 hc1 (hA7' _ hc1), Th2.aVal_of_C2 hc2 (hA7' _ hc2)]
      omega
    · rw [Th2.aVal_of_other hc1 hn1, Th2.aVal_of_other hc2 hn2]
      omega

theorem exists_isV2StarTriple [Finite G] (hA7 : B_A7_notC2)
    (hex : ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) :
    ∃ (x y : G) (K : Subgroup G), IsV2StarTriple x y K := by
  classical
  obtain ⟨x₀, y₀, K₀, h₀⟩ := hex
  let s1 : Set (G × G × Subgroup G) := {t | IsV2Triple t.1 t.2.1 t.2.2}
  obtain ⟨t₁, ht₁, hm1⟩ := Set.exists_max_image s1 (fun t => Th2.muVal t.2.2) (Set.toFinite s1)
    ⟨(x₀, y₀, K₀), h₀⟩
  have hV1 : V2Max1 t₁.1 t₁.2.1 t₁.2.2 := ⟨ht₁, fun x' y' K' h' hs =>
    absurd (hm1 (x', y', K') h') (not_le.2 (Th2.muVal_lt_of_u2Succ hA7 hs))⟩
  let s2 : Set (G × G × Subgroup G) := {t | V2Max1 t.1 t.2.1 t.2.2}
  obtain ⟨t₂, ht₂, hm2⟩ := Set.exists_max_image s2 (fun t => pRank 2 ↥(CxK t.1 t.2.2))
    (Set.toFinite s2) ⟨t₁, hV1⟩
  have hV2 : V2Max2 t₂.1 t₂.2.1 t₂.2.2 := ⟨ht₂, fun x' y' K' h' => hm2 (x', y', K') h'⟩
  let s3 : Set (G × G × Subgroup G) := {t | V2Max2 t.1 t.2.1 t.2.2}
  obtain ⟨t₃, ht₃, hm3⟩ := Set.exists_max_image s3 (fun t => twoPartCard (CxK t.1 t.2.2))
    (Set.toFinite s3) ⟨t₂, hV2⟩
  have hV3 : V2Max3 t₃.1 t₃.2.1 t₃.2.2 := ⟨ht₃, fun x' y' K' h' => hm3 (x', y', K') h'⟩
  let s4 : Set (G × G × Subgroup G) := {t | V2Max3 t.1 t.2.1 t.2.2}
  obtain ⟨t₄, ht₄, hm4⟩ := Set.exists_max_image s4 (fun t => twoPartCard (NxK t.1 t.2.2))
    (Set.toFinite s4) ⟨t₃, hV3⟩
  exact ⟨t₄.1, t₄.2.1, t₄.2.2, ht₄, fun x' y' K' h' => hm4 (x', y', K') h'⟩

end Max

theorem b_thm2_v2ss_of (hA7 : B_A7_notC2) (h : B_thm2_v2star_ss) : B_thm2_v2ss := by
  intro G _ _ hG hex
  exact h G hG (exists_isV2StarTriple hA7 hex)

end CFSG.GH74.GLS
