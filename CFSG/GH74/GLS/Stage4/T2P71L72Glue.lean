module

public import CFSG.GH74.GLS.Stage4.T2P71Defs
public import CFSG.GH74.GLS.Stage4.T2P51
public import CFSG.GH74.GLS.Stage4.T2P52Done
public import CFSG.GH74.GLS.Stage4.T2P53

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex

namespace CFSG.GH74.GLS.Stage4.Rest

@[expose] def P71L72Env : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (n : ℕ) (N : T2N3 G) (u : G),
    P71Env Gs n N u → ∀ P : Sylow 3 G, (P : Subgroup G) ≤ centralizer ({N.z} : Set G) →
      (P : Subgroup G) ≤ N.K₁ ⊔ N.K₂

theorem p71L72_of_env
    (h : P71L72Env) : P71L72 := by
  intro G _ _ hStd hr Gs _ n hn hAt z K₁ K₂ F₁ F₂ _ _ t hSet hRem P hP
  obtain ⟨N₁, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
    ch6T2P51 G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem rfl
  obtain ⟨F, hF5⟩ := ch6T2P52 G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem N₁ u hz hK₁ hK₂ hq₁ hq₂
    hLoc hCoord
  obtain ⟨a, hau, hWeyl⟩ := ch6T2P53 G hr Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ t hSet hRem
    (⟨N₁, F⟩ : T2N2 G) u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord hF5
  let N : T2N3 G := ⟨⟨N₁, F⟩, a⟩
  have hSec : Ch6Sec5 N u := ⟨hLoc, hF5, hWeyl, hau⟩
  have henv : P71Env Gs n N u :=
    { std := hStd
      rank := hr
      n_ge := hn
      at_ := hAt
      q₁ := hq₁
      q₂ := hq₂
      coord := hCoord
      sec5 := hSec
      setup := ⟨F₁, F₂, ‹_›, ‹_›, t, by
        have h1 : N.z = z := hz
        have h2 : N.K₁ = K₁ := hK₁
        have h3 : N.K₂ = K₂ := hK₂
        rw [h1, h2, h3]
        exact ⟨hSet, hRem⟩⟩ }
  have hNz : N.z = z := hz
  have hNK₁ : N.K₁ = K₁ := hK₁
  have hNK₂ : N.K₂ = K₂ := hK₂
  have := h G Gs n N u henv P (by rw [hNz]; exact hP)
  rw [hNK₁, hNK₂] at this
  exact this

end CFSG.GH74.GLS.Stage4.Rest
