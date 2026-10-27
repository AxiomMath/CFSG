module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx25
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx13
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx21
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx24

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem card_P₁_of (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {m : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (m + 1)) : Nat.card ↥(Pof S K₁) = 2 ^ (m + 2) := by
  have hV := hs.card_V₁ hII hq
  rw [← hV, hk]
  ring

theorem g2TermType_of_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) (hSyl : G2_Sylow_shape) (hC1 : C1_of_Fused)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 2)
    (hSS : S = S1 S K₁) {m : ℕ} (hm : 1 ≤ m) (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (m + 1)) :
    G2TermType G z S := by
  obtain ⟨a, t, y, hshape, -, -⟩ := hs.g2shape_of_S1 hII hq hrec he hSS hm hk
  have hPcard := hs.card_P₁_of hII hq hk
  have hrelS : (Pz S z).relIndex S = 2 := by
    rw [← hSS] at he
    exact he
  obtain ⟨e, he', hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  obtain ⟨q, ⟨p, f, hp, hp2, hpf, hqfac⟩, hSL2⟩ := hC1 G z S K₁ K₂ hs.fused hSS hrelS hNN
  have hfac : (Nat.card ↥(Pof S K₁)).factorization 2 = m + 2 := by
    rw [hPcard, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  rw [hfac] at hqfac
  have hf : 0 < f := by
    by_contra hf0
    have hf0' : f = 0 := by omega
    rw [hf0', pow_zero] at hpf
    rw [← hpf] at hqfac
    simp at hqfac
  obtain ⟨Gs, instG, instF, hL, S', hiso⟩ :=
    hSyl G S (Aof S K₁ W₂ h) a t y (m + 1) (by omega) hshape p f hp hp2 hf (by rw [hpf]; omega)
  exact ⟨q, ⟨Gs, instG, instF, p, f, hp, hp2, hpf, hL, S', hiso⟩, hs.one_class hII h31 hrelS, hSL2⟩

end Setup8

theorem lemma_8_4 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) (hSyl : G2_Sylow_shape) (hC1 : C1_of_Fused) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G),
      Setup8 G z S K₁ K₂ W₁ W₂ U u h → 16 ≤ Nat.card ↥(Pof S K₁) → G2TermType G z S := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h hs hP16
  obtain ⟨he, -, -⟩ := (lemma_8_3 hII hq hrec G z S K₁ K₂ W₁ W₂ U u h hs).2 hP16
  obtain ⟨k, hk2, hk⟩ := hs.exists_k hII hq
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hPcard := hs.card_P₁_of hII hq hk
  have hm : 2 ≤ m := by
    by_contra hm
    have h1 : 2 ^ (m + 2) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hSS := hs.S_eq_S1 hII hq hrec he hm hk
  exact hs.g2TermType_of_S1 hII hq hrec h31 hSyl hC1 he hSS (by omega) hk

theorem case8_64 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h31 : IVK_3_1a_lifted) (hSyl : G2_Sylow_shape) (hC1 : C1_of_Fused) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G),
      Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → Nat.card ↥S = 2 ^ 6 →
        G2TermType G z S := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h hs hP8 hS64
  obtain ⟨hP₂, hcases⟩ := hs.cases8_aux hII hq hrec hP8
  rcases hcases with ⟨hSS, -, hQ₁, hQ₂⟩ | ⟨-, hc, -, -⟩ | ⟨-, hc, -, -⟩
  · obtain ⟨e, he', hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
    have he1 : e = 1 := by
      rw [hQ₂, hP8] at hq2
      omega
    subst he1
    have he : (Pz S z).relIndex (S1 S K₁) = 2 := by omega
    have hV := hs.card_V₁ hII hq
    have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
    exact hs.g2TermType_of_S1 hII hq hrec h31 hSyl hC1 he hSS (le_refl 1) hk
  · rw [hS64] at hc
    omega
  · rw [hS64] at hc
    omega

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
