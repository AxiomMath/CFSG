module

public import CFSG.ClassicalInvolution.WeakCT.SpSpCharts
import CFSG.ClassicalInvolution.WeakCT.SymplecticTwo

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock)

theorem weakCT_symplectic_two_of_spSpCharts {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2) {G : Type} [Group G] (κ₁ κ₂ : StatedSp (s + 2) F →* G)
    (hκ₁ : Function.Injective κ₁) (hκ₂ : Function.Injective κ₂)
    (hagree : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong : (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (hcross₁ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₂ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a) :
    ∃ Ψ : StatedSp (s + 3) F →* G, Ψ.ker ≤ Subgroup.center (StatedSp (s + 3) F) ∧
      Ψ.range = κ₁.range ⊔ κ₂.range := by
  obtain ⟨U, hcomm, hpair, hsp, hgens⟩ :=
    exists_chain_of_spSpCharts hs κ₁ κ₂ hκ₁ hκ₂ hagree hlong hcross₁ hcross₂
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_two (by omega) hF U hcomm hpair hsp
  exact ⟨Ψ, hker, hrange.trans hgens⟩

theorem weakCT_symplectic_two_of_three_spSpCharts {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2) {G : Type} [Group G] (κ₁ κ₂ κ₃ : StatedSp (s + 2) F →* G)
    (hκ₁ : Function.Injective κ₁) (hκ₂ : Function.Injective κ₂) (hκ₃ : Function.Injective κ₃)
    (hagree₁₂ : ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong₁₂ : (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (hagree₂₃ : ∀ k : Fin s,
      (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range)
    (hlong₂₃ : (κ₂.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₃.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (hcross₁₂ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₂.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₁₃ₛ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₁₃ₗ : ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a)
    (hcross₂₃ₛ : ∀ a ∈ (κ₂.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
        a * b = b * a)
    (hcross₂₃ₗ : ∀ a ∈ (κ₂.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
      ∀ b ∈ (κ₃.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a) :
    ∃ Ψ : StatedSp (s + 4) F →* G, Ψ.ker ≤ Subgroup.center (StatedSp (s + 4) F) ∧
      Ψ.range = κ₁.range ⊔ κ₂.range ⊔ κ₃.range := by
  obtain ⟨U, hcomm, hpair, hsp, hgens⟩ :=
    exists_chain_of_three_spSpCharts hs κ₁ κ₂ κ₃ hκ₁ hκ₂ hκ₃ hagree₁₂ hlong₁₂ hagree₂₃ hlong₂₃
      hcross₁₂ hcross₁₃ₛ hcross₁₃ₗ hcross₂₃ₛ hcross₂₃ₗ
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_two (by omega) hF U hcomm hpair hsp
  exact ⟨Ψ, hker, hrange.trans hgens⟩

end CFSG.ClassicalInvolution.WeakCT

end
