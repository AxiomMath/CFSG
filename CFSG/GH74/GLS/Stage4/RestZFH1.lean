module

public import CFSG.GH74.GLS.Stage4.RestZFDef
public import CFSG.GH74.GLS.Stage4.T9Final
public import CFSG.GH74.GLS.Stage4.T6Final

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank

@[expose] def Ch6RestT2SH : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) →
        ∃ D : Ch6Notation G, Ch6Pre D ∧ Ch6S6 D ∧ D.HIdx

theorem ch6RestT2SH_of_steps''' (h1 : Ch6T2Rem) (h2 : Ch6T2Num)
    (h3 : Ch6T2P51) (h4 : Ch6T2P52) (h5 : Ch6T2P53) (h5' : Ch6T2SLe) (h6 : Ch6T2Sec6')
    (hTS : Ch6T2TSing) : Ch6RestT2SH := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn
  obtain ⟨z, K₁, K₂, F₁, F₂, iF₁, iF₂, hSet⟩ := ch6_setup hr hAt
  obtain ⟨t, hRem⟩ := h1 G hStd hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ hSet
  obtain ⟨p, hp, hp2, ⟨m, hm⟩, ⟨n, hn'⟩, hrel⟩ := h2 G hStd hr Gs q₁ q₂ hAt h99 hn
  have hNum : Ch6NumD p q₁ q₂ := ⟨hp, hp2, ⟨m, hm⟩, ⟨n, hn'⟩, hrel⟩
  have core : ∀ (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂],
      Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t → Ch6TSing p q₂ z K₁ K₂ →
        ∃ D : Ch6Notation G, Ch6Pre D ∧ Ch6S6 D ∧ D.HIdx := by
    intro K₁ K₂ F₁ F₂ _ _ hSet hRem hts
    have hmod : q₁ % 4 = q₂ % 4 := by
      rcases hrel with h | h
      · rw [h]
      · rw [h]; exact pow_three_mod_four_of_odd hSet.odd₂
    obtain ⟨N₁, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
      h3 G Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem hmod
    obtain ⟨F, hF5⟩ := h4 G Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem N₁ u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
    obtain ⟨a, hau, hWeyl⟩ :=
      h5 G hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem (⟨N₁, F⟩ : T2N2 G) u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
        hF5
    let N₃ : T2N3 G := ⟨⟨N₁, F⟩, a⟩
    have hSle : N₃.S ≤ ⨆ n ∈ N₃.Nsub, conjBy n (N₃.K₁ ⊔ N₃.K₂) :=
      h5' G hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem N₃ u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord hF5 hWeyl
    have hSec₃ : Ch6Sec5 N₃ u := ⟨hLoc, hF5, hWeyl, hau⟩
    obtain ⟨P₀, P, hS6⟩ := h6 G hStd hr Gs q₁ q₂ hAt h99 hn z K₁ K₂ F₁ F₂ t hSet hRem N₃ u p hz hK₁ hK₂
      hq₁ hq₂ hNum hts hCoord hSec₃
    let N₄ : T2N4 G := ⟨N₃, p, P₀, P⟩
    have hNum₄ : Ch6NumD N₄.p N₄.q₁ N₄.q₂ := by
      show Ch6NumD p N₁.q₁ N₁.q₂
      rw [hq₁, hq₂]
      exact hNum
    have hShape : Ch6Shape N₄.toCh6 :=
      ch6T2Sec9'_proved G hStd hr Gs q₁ q₂ hAt h99 hn z K₁ K₂ F₁ F₂ t hSet hRem N₄ u hz hK₁ hK₂ hq₁ hq₂
        (by rw [hq₁, hq₂] at hNum₄; exact hNum₄) hCoord hSec₃ hS6
    have hH : N₄.toCh6.HIdx := hLoc.H_idx
    exact ⟨N₄.toCh6, Ch6Pre.of_stages hNum₄ hSec₃ hSle hS6 hShape, hS6, hH⟩
  rcases hTS G hStd hr Gs q₁ q₂ hAt h99 hn z K₁ K₂ F₁ F₂ t hSet hRem p hNum with hts | ⟨hq, hts⟩
  · exact core K₁ K₂ F₁ F₂ hSet hRem hts
  · exact core K₂ K₁ F₂ F₁ (hSet.swap hq) hRem.swap hts

end CFSG.GH74.GLS.Stage4.Rest

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2

theorem ch6RestT2SH_of_steps''' (h11b : IVK_11_1b_nat) (h1 : Ch6T2Rem)
    (h2 : Ch6T2Num) (h3 : Ch6T2P51) (h4 : Ch6T2P52) (h5 : Ch6T2P53) (h5' : Ch6T2SLe)
    (hTS : Ch6T2TSing) : Ch6RestT2SH :=
  Rest.ch6RestT2SH_of_steps''' h1 h2 h3 h4 h5 h5' (ch6T2Sec6'_proved h11b) hTS

end CFSG.GH74.GLS.Stage4.Rest.T6
