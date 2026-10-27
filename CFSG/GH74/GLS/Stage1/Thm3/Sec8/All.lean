module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Rank3
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

theorem prop_8_1_of_closed (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6) (hset : Setup8_exists) (h31 : IVK_3_1a_lifted)
    (hSyl : G2_Sylow_shape) (hC1 : C1_of_Fused) (h86 : Lemma8_6) (hY : Y34_E) (h89 : Lemma8_9)
    (h810 : Lemma8_10) (hfin : Final81) : Prop8_1 := by
  intro G _ _ z S K₁ K₂ hstd hfus
  have key : ∀ K₁ K₂ : Subgroup G, Fused8 G z S K₁ K₂ → G2TermType G z S ∨ L4U4TermType G z S := by
    intro K₁ K₂ hf
    obtain ⟨W₁, W₂, U, u, h, hs⟩ := hset G z S K₁ K₂ hf
    by_cases hcase : Nat.card ↥(Pof S K₁) = 8 → S = S1 S K₁
    · exact Or.inl (hs.g2TermType_of_not_swap hII hq hrec h31 hSyl hC1 hcase)
    · right
      push Not at hcase
      obtain ⟨hP8, hSne⟩ := hcase
      obtain ⟨-, hcases⟩ := hs.cases8_aux hII hq hrec hP8
      have hS7 : 2 ^ 7 ≤ Nat.card ↥S := by
        rcases hcases with ⟨hSS, -⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩
        · exact absurd hSS hSne
        · exact hc.ge
        · rw [hc]
          norm_num
      obtain ⟨Y, D, t, w, hC⟩ := h86 G z S K₁ K₂ W₁ W₂ U u h hs hP8 hS7
      have hYS : Y ≤ S := by
        rw [hC.2.1]
        exact le_sup_left
      have hV := hs.card_V₁ hII hq
      have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ 2 := by norm_num; omega
      have hUY : U ≤ Y := (hs.U_le_A hII hq hrec (le_refl 2) hk).trans hC.2.2.1.1
      have hnormed : NormedBy U Y := fun x hx a ha => hs.U_norm x (hYS hx) a ha
      obtain ⟨E₁, E₂, hE⟩ := hY G Y U hC.2.2.1.2.2.2.1 hUY hs.U_four hnormed
      have hS : Nat.card ↥S = 2 ^ 7 :=
        h89 G z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS7 hC E₁ E₂ hE
      obtain ⟨Sg, hSg⟩ := h810 G z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS hC E₁ E₂ hE
      exact hfin G z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS hC E₁ E₂ hE ⟨Sg, hSg⟩
  rcases labelling_exists S K₁ K₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact key K₁ K₂ (fused8_of_std4 h41 h61 h66 hstd hfus h1 h2)
  · exact key K₂ K₁ (fused8_of_std4 h41 h61 h66 (std4_swap hstd) hfus h1 h2)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
