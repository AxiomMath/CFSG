module

public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

@[expose] def SecOfG (G : Type) [Group G] (z : G) (B : Type) [Group B] (b : B) : Prop :=
  ∃ (H₀ : Subgroup G) (H₁ : Subgroup ↥H₀) (hn : H₁.Normal) (hz : z ∈ H₀), H₀ ≠ ⊤ ∧ Odd (Nat.card ↥H₁) ∧
    ∃ e : @Sec G _ H₀ H₁ hn ≃* B, e (@zSec G _ z H₀ hz H₁ hn) = b

theorem SecOfG.of_sec {G : Type} [Group G] {z : G} {H₀ : Subgroup G} {H₁ : Subgroup ↥H₀} [H₁.Normal]
    (hz : z ∈ H₀) (hH₀ : H₀ ≠ ⊤) (hodd : Odd (Nat.card ↥H₁)) :
    SecOfG G z (Sec H₀ H₁) (zSec z H₀ hz H₁) :=
  ⟨H₀, H₁, inferInstance, hz, hH₀, hodd, MulEquiv.refl _, rfl⟩

theorem SecOfG.of_sig4B {G : Type} [Group G] {z : G} {H₀ : Subgroup G} {H₁ : Subgroup ↥H₀} [H₁.Normal]
    {hz : z ∈ H₀} {p : ℕ} {X : Subgroup (Sec H₀ H₁)} (h : Sig4B G z H₀ H₁ hz p X) :
    SecOfG G z (Sec H₀ H₁) (zSec z H₀ hz H₁) :=
  SecOfG.of_sec hz h.proper h.odd

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
