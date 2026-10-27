module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf13H3A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf12Vertex

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B

@[expose] def CentralizeH : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) [Fact (P24.Hyp51TwinInnerAt Ω)],
    HCtx Ω K K' W S R R' z u →
    ∃ (H' : HCtx Ω K K' W S R R' z u) (S₁ : Sylow 2 G),
      (S₁ : Subgroup G) ≤ Subgroup.normalizer (W : Set G) ∧ R ≤ (S₁ : Subgroup G) ∧
      R' ≤ (S₁ : Subgroup G) ∧ H'.a ∈ Subgroup.centralizer ((S₁ : Subgroup G) : Set G) ∧
      ∀ y ∈ MGrp Ω W, H'.a * y * H'.a⁻¹ * y⁻¹ ∈ OCW W

@[expose] def TransCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z u : G) [Fact (P24.Hyp51TwinInnerAt Ω)]
    (H : HCtx Ω K K' W S R R' z u) (S₁ : Sylow 2 G),
    (S₁ : Subgroup G) ≤ Subgroup.normalizer (W : Set G) → R ≤ (S₁ : Subgroup G) →
      R' ≤ (S₁ : Subgroup G) → H.a ∈ Subgroup.centralizer ((S₁ : Subgroup G) : Set G) →
      (∀ y ∈ MGrp Ω W, H.a * y * H.a⁻¹ * y⁻¹ ∈ OCW W) → H.TransH0

theorem h3_of_transCentral [Fact P24.Sup23_2P] (hA : CentralizeH) (hB : TransCentral) : H3 := by
  intro G _ _ _ Ω K K' W S R R' z u hI hyp h8 D hK hK' hR hR' a ha2 haR haR' T₃ hT hTN hTa
  by_contra ha1
  have hs := hyp.std.setting
  have hd := hyp.data
  have hz : D.F.z = z := (hs.hz.eq (hK ▸ D.F.hz)).symm
  let C : Ctx8F Ω K K' W S R R' z u :=
    { toCtx8 := ⟨hs, hd, h8, D, hK, hK', hR, hR', hz⟩
      fuse := fun hF => fun h₁ h₁1 h₁z h₁2 h₂ h₂1 h₂z h₂2 =>
        hF G Ω K K' z hyp.std _ _ h₁ h₁1 h₁z h₁2 h₂ h₂1 h₂z h₂2
      hyp := hyp }
  let H : HCtx Ω K K' W S R R' z u := ⟨C, a, T₃, ha2, ha1, haR, haR', hT, hTN, hTa⟩
  obtain ⟨H', S₁, hS₁W, hRS₁, hR'S₁, haS₁, haZ⟩ := hA G Ω K K' W S R R' z u H
  haveI : Fact P24.Hyp51VertexP := ⟨P24.hyp51VertexP_proved⟩
  exact H'.false_of_transH0 (hB G Ω K K' W S R R' z u H' S₁ hS₁W hRS₁ hR'S₁ haS₁ haZ)

end S24B
end Asc77
end CFSG.ClassicalInvolution.Q8P

