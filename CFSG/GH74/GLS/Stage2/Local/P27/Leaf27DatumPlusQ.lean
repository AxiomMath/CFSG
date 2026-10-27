module

public import CFSG.GH74.GLS.Stage1.Main.BridgeField
public import CFSG.GH74.GLS.Stage2.Local.P27.L4LayerA

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Main

variable {G : Type} [Group G] [Finite G]

@[expose] def P27DatumPlusQ (z : G) (S : Subgroup G) (k : Kind) : Prop :=
  (k = Kind.psp4 → ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1PSp4 G z S q L₁ L₂ →
      ∃ x : G, DatumPlusQ z x q) ∧
    (∀ ε : Bool, k = Kind.l4 ε → ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      Stage1L4 G z S ε q L₁ L₂ → (∃ x₀ ∈ Cen z, IsNonCentralInvolution x₀) →
        ∃ x : G, DatumPlusQ z x q)

@[expose] def P27DatumPlusQL4 (z : G) (S : Subgroup G) (k : Kind) : Prop :=
  ∀ ε : Bool, k = Kind.l4 ε → ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
    Stage1L4 G z S ε q L₁ L₂ → (∃ x₀ ∈ Cen z, IsNonCentralInvolution x₀) →
      ∃ x : G, DatumPlusQL4 z x q

theorem p27DatumPlusQL4_of_data {z : G} {S : Subgroup G} {k : Kind}
    (hfld : L4TwoFieldStmt G z k S) (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z))
    (hK : KGH G) (hSch : P34.GHSchreier) : P27DatumPlusQL4 z S k := by
  intro ε hk q L₁ L₂ h4 hx₀
  rcases h4.fusion with ⟨-, hone⟩ | ⟨hq4, x, hx, -, -⟩
  · obtain ⟨x₀, -, hx₀⟩ := hx₀
    exact absurd (isCentralInvolution_of_isConj_P27 hz (hone z x₀ hz.1 hx₀.1)) hx₀.2
  · exact datumPlusQL4_of_stage1_l4 hK hSch hz hS h4.pair h4.index_le hx
      (hfld ε q L₁ L₂ x hk h4 hx hq4)

end CFSG.GH74.GLS.Stage2.Local.P27
