module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AFive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def S172AExist : Prop :=
  ∀ n : ℕ, Odd n → 7 ≤ n →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D K : Subgroup Ω) (x : Ω), Cfg172 3 S B D K x →
      catalogIs (PSimple 3 S) (isLnA n 2) → catalogIs (PSimple 3 K) (isLnA ((n - 1) / 2) 4) →
      ∃ D₁ K₁ : Subgroup Ω, GLAStdSubPre 3 B x S D₁ K₁ ∧ catalogIs (PSimple 3 K₁) (isLnA (n - 2) 2)

@[expose] def S172ALayer : Prop :=
  ∀ n : ℕ, Odd n → 7 ≤ n →
    ∀ (Ω : Type) [Group Ω] [Finite Ω] (S B D K : Subgroup Ω) (x : Ω), Cfg172 3 S B D K x →
      catalogIs (PSimple 3 S) (isLnA n 2) → catalogIs (PSimple 3 K) (isLnA ((n - 1) / 2) 4) →
      ∀ D₁ K₁ : Subgroup Ω, GLAStdSubPre 3 B x S D₁ K₁ → catalogIs (PSimple 3 K₁) (isLnA (n - 2) 2) →
        catalogIs (PSimple 3 (GLALayer (S ⊓ cs (D ⊔ D₁)))) (isLnA ((n - 3) / 2) 4)

theorem S172FactA_of_residuals (hb : CatDistinct.OrderBridge) (hE : S172AExist) (hL : S172ALayer) :
    S172FactA := by
  intro n hn Ω _ _ S B D K x hcfg hS hK
  by_cases h7 : 7 ≤ n
  · obtain ⟨D₁, K₁, hpre, hK₁⟩ := hE n hn h7 Ω S B D K x hcfg hS hK
    exact ⟨D₁, K₁, hpre, hK₁, hL n hn h7 Ω S B D K x hcfg hS hK D₁ K₁ hpre hK₁⟩
  · have hn' : n = 1 ∨ n = 3 ∨ n = 5 := by
      obtain ⟨k, hk⟩ := hn
      omega
    rcases hn' with rfl | rfl | rfl
    · exact (not_catalogIs_isLnA_one _ 2 hS).elim
    · have h1 : (3 - 1) / 2 = 1 := by norm_num
      rw [h1] at hK
      exact (not_catalogIs_isLnA_one _ 4 hK).elim
    · have h2 : (5 - 1) / 2 = 2 := by norm_num
      rw [h2] at hK
      exact (S172A.five_false hb hcfg hK).elim

end CFSG.LocalAnalysis.GLTheoremA.S172A

end
