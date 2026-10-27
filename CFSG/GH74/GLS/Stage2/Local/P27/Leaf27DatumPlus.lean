module

public import CFSG.GH74.GLS.Stage2.Local.P27.Ps4LayerA
public import CFSG.GH74.GLS.Stage2.Local.P27.L4LayerA
public import CFSG.GH74.GLS.Stage1.Main.BridgeField

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Main

variable {G : Type} [Group G] [Finite G]

@[expose] def P27DatumPlus (z : G) (k : Kind) : Prop :=
  IsClassicalKind k → (∃ x₀ ∈ Cen z, IsNonCentralInvolution x₀) → ∃ x : G, DatumPlus z x

theorem leaf_p27datumPlus_of_ctx
    {Ctx : ∀ (G : Type) [Group G] [Finite G], G → Kind → Subgroup G → Prop}
    (hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → L4TwoFieldStmt G z k S)
    (hdata : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → Stage1Data G z S k)
    (hcen : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → IsCentralInvolution z)
    (hsyl : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → IsSylowOf 2 S (Cen z))
    (hkgh : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G),
      Ctx G z k S → KGH G)
    (hSch : P34.GHSchreier) : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Ctx G z k S → P27DatumPlus z k := by
  intro G _ _ z k S hctx hcl hx₀
  have hd := hdata G z k S hctx
  have hz := hcen G z k S hctx
  have hS := hsyl G z k S hctx
  have hK := hkgh G z k S hctx
  rcases hcl with rfl | ⟨ε, rfl⟩
  · cases hd with
    | psp4 h =>
      obtain ⟨q, L₁, L₂, h4⟩ := h
      obtain ⟨x₀, hx⟩ := h4.two
      exact datumPlus_of_stage1_psp4 hK hSch hz hS h4 hx
  · cases hd with
    | l4 _ h =>
      obtain ⟨q, L₁, L₂, h4⟩ := h
      rcases h4.fusion with ⟨-, hone⟩ | ⟨hq4, x, hx, -, -⟩
      · obtain ⟨x₀, -, hx₀⟩ := hx₀
        exact absurd (isCentralInvolution_of_isConj_P27 hz (hone z x₀ hz.1 hx₀.1)) hx₀.2
      · exact datumPlus_of_stage1_l4 hK hSch hz hS h4.pair h4.index_le hx
          (hfld G z (Kind.l4 ε) S hctx ε q L₁ L₂ x rfl h4 hx hq4)

end CFSG.GH74.GLS.Stage2.Local.P27
