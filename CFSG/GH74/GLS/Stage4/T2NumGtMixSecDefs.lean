module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixSteps

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank

@[expose] def Ch6MixLoc : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁]
      [Field F₂] (t : G), Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
        q₂ < q₁ → q₁ % 4 ≠ q₂ % 4 →
          ∃ (N : T2N1 G) (u : G), N.z = z ∧ N.K₁ = K₁ ∧ N.K₂ = K₂ ∧ N.q₁ = q₁ ∧ N.q₂ = q₂ ∧
            Ch6Loc5M N u ∧ Ch6Coord2 N

@[expose] def Ch6MixF5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁]
      [Field F₂] (t : G), Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
        q₂ < q₁ → q₁ % 4 ≠ q₂ % 4 →
          ∀ (N : T2N1 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
            Ch6Loc5M N u → Ch6Coord2 N →
              ∃ N2 : T2N2 G, N2.toT2N1 = N ∧ Ch6F5W N2

@[expose] def Ch6MixWeyl : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁]
      [Field F₂] (t : G), Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
        q₂ < q₁ → q₁ % 4 ≠ q₂ % 4 →
          ∀ (N : T2N1 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
            Ch6Loc5M N u → Ch6Coord2 N →
              ∀ N2 : T2N2 G, N2.toT2N1 = N → Ch6F5W N2 →
                ∃ N3 : T2N3 G, N3.toT2N2 = N2 ∧ Ch6Weyl N3 ∧ N3.u = u

theorem ch6Mix_secEx_of_steps (hL : Ch6MixLoc) (hF : Ch6MixF5) (hW : Ch6MixWeyl) : Ch6MixSecEx := by
  intro G _ _ hr Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem hlt hmod
  obtain ⟨N, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ := hL G hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem hlt hmod
  obtain ⟨N2, hN2, hF5⟩ := hF G hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem hlt hmod N u hz hK₁ hK₂ hq₁ hq₂
    hLoc hCoord
  obtain ⟨N3, hN3, hWey, hu⟩ := hW G hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem hlt hmod N u hz hK₁ hK₂ hq₁ hq₂
    hLoc hCoord N2 hN2 hF5
  have hN : N3.toT2N2.toT2N1 = N := by rw [hN3, hN2]
  refine ⟨N3, u, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, hWey, hu⟩, ?_⟩
  · rw [← hz, ← hN]
  · rw [← hK₁, ← hN]
  · rw [← hK₂, ← hN]
  · rw [← hq₁, ← hN]
  · rw [← hq₂, ← hN]
  · rw [hN]; exact hLoc
  · rw [hN3]; exact hF5
  · rw [hN]; exact hCoord

end CFSG.GH74.GLS.Stage4.Rest
