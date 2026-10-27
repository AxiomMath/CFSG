module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx34
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx26

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

@[expose] def Prop8_1Rank3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    CFSG.pRank 2 G ≤ 3 → (∃ u ∈ Pz S z, IsConj z u ∧ u ≠ z) → G2TermType G z S

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem lemma_8_6_rank3 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hrank : CFSG.pRank 2 G ≤ 3) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    (hP8 : Nat.card ↥(Pof S K₁) = 8) : S = S1 S K₁ := by
  by_contra hne
  have h4 := hs.rank_ge_four_of_ne hII hq hrec hP8 hne
  omega

theorem g2TermType_of_not_swap (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) (hSyl : G2_Sylow_shape) (hC1 : C1_of_Fused)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hnot : Nat.card ↥(Pof S K₁) = 8 → S = S1 S K₁) :
    G2TermType G z S := by
  obtain ⟨k, hk2, hk⟩ := hs.exists_k hII hq
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hPcard := hs.card_P₁_of hII hq hk
  by_cases hm : m = 1
  · subst hm
    have hP8 : Nat.card ↥(Pof S K₁) = 8 := by rw [hPcard]; norm_num
    have hSS := hnot hP8
    obtain ⟨-, hcases⟩ := hs.cases8_aux hII hq hrec hP8
    rcases hcases with ⟨-, hS64, -, -⟩ | ⟨hne, -, -, -⟩ | ⟨hne, -, -, -⟩
    · exact case8_64 hII hq hrec h31 hSyl hC1 G z S K₁ K₂ W₁ W₂ U u h hs hP8 hS64
    · exact absurd hSS hne
    · exact absurd hSS hne
  · have hP16 : 16 ≤ Nat.card ↥(Pof S K₁) := by
      rw [hPcard]
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lemma_8_4 hII hq hrec h31 hSyl hC1 G z S K₁ K₂ W₁ W₂ U u h hs hP16

theorem g2TermType_of_rank3 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) (hSyl : G2_Sylow_shape) (hC1 : C1_of_Fused)
    (hrank : CFSG.pRank 2 G ≤ 3) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) : G2TermType G z S :=
  hs.g2TermType_of_not_swap hII hq hrec h31 hSyl hC1 fun hP8 =>
    hs.lemma_8_6_rank3 hII hq hrec hrank hP8

end Setup8

theorem std4_swap {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}
    (h : Std4 G z S K₁ K₂) : Std4 G z S K₂ K₁ :=
  { h with
    comps := by rw [h.comps]; exact Set.pair_comm K₁ K₂
    ne := h.ne.symm }

theorem fused8_of_std4 (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6) {G : Type} [Group G] [Finite G]
    {z : G} {S K₁ K₂ : Subgroup G} (hstd : Std4 G z S K₁ K₂)
    (hfus : ∃ u ∈ Pz S z, IsConj z u ∧ u ≠ z) (hord₁ : Nat.card ↥(Pof S K₂) ≤ Nat.card ↥(Pof S K₁))
    (hord₂ : Nonempty (↥(Pof S K₁) ≃* ↥(Pof S K₂)) → Nat.card ↥(Qof S K₁) ≤ Nat.card ↥(Qof S K₂)) :
    Fused8 G z S K₁ K₂ := by
  have hs6 : Std6 G z S := ⟨hstd.simple, hstd.rank, hstd.rank_le, hstd.gen4, hstd.classical, hstd.thm2, hstd.sylow, hstd.kgh⟩
  obtain ⟨ha, hb, -, hd⟩ := h61 G z S hs6
  have hr₁ := hstd.comp_rigid (K := K₁) (Or.inl rfl)
  have hr₂ := hstd.comp_rigid (K := K₂) (Or.inr rfl)
  obtain ⟨hQ, -, -⟩ := h41 G z S K₁ K₂ hstd
  have hp66 := h66 G z S K₁ K₂ hstd (ha K₁ hr₁) (ha K₂ hr₂) (hb K₁ hr₁) (hb K₂ hr₂)
  exact ⟨hstd, ha K₁ hr₁, ha K₂ hr₂, hb K₁ hr₁, hb K₂ hr₂, hd K₁ hr₁, hd K₂ hr₂, hQ, hp66, hfus,
    hord₁, hord₂⟩

theorem labelling_exists {G : Type} [Group G] [Finite G] (S K₁ K₂ : Subgroup G) :
    (Nat.card ↥(Pof S K₂) ≤ Nat.card ↥(Pof S K₁) ∧
        (Nonempty (↥(Pof S K₁) ≃* ↥(Pof S K₂)) → Nat.card ↥(Qof S K₁) ≤ Nat.card ↥(Qof S K₂))) ∨
      (Nat.card ↥(Pof S K₁) ≤ Nat.card ↥(Pof S K₂) ∧
        (Nonempty (↥(Pof S K₂) ≃* ↥(Pof S K₁)) → Nat.card ↥(Qof S K₂) ≤ Nat.card ↥(Qof S K₁))) := by
  by_cases h1 : Nat.card ↥(Pof S K₂) ≤ Nat.card ↥(Pof S K₁) ∧
      (Nonempty (↥(Pof S K₁) ≃* ↥(Pof S K₂)) → Nat.card ↥(Qof S K₁) ≤ Nat.card ↥(Qof S K₂))
  · exact Or.inl h1
  · right
    rw [not_and_or] at h1
    rcases h1 with h1 | h1
    · refine ⟨by omega, fun ⟨e⟩ => ?_⟩
      have := Nat.card_congr e.toEquiv
      omega
    · push Not at h1
      obtain ⟨⟨e⟩, hQ⟩ := h1
      have hP := Nat.card_congr e.toEquiv
      refine ⟨by omega, fun _ => by omega⟩

theorem prop_8_1_rank3 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6) (hset : Setup8_exists)
    (h31 : IVK_3_1a_lifted) (hSyl : G2_Sylow_shape) (hC1 : C1_of_Fused) : Prop8_1Rank3 := by
  intro G _ _ z S K₁ K₂ hstd hrank hfus
  have key : ∀ K₁ K₂ : Subgroup G, Fused8 G z S K₁ K₂ → G2TermType G z S := by
    intro K₁ K₂ hf
    obtain ⟨W₁, W₂, U, u, h, hs⟩ := hset G z S K₁ K₂ hf
    exact hs.g2TermType_of_rank3 hII hq hrec h31 hSyl hC1 hrank
  rcases labelling_exists S K₁ K₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key K₁ K₂ (fused8_of_std4 h41 h61 h66 hstd hfus h1 h2)
  · exact key K₂ K₁ (fused8_of_std4 h41 h61 h66 (std4_swap hstd) hfus h1 h2)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
