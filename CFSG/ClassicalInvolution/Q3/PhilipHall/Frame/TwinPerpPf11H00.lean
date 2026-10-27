module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf7A01

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P.P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q8P.Asc77
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer (tqMembers exactCore)

section Residuals

@[expose] def Sup23_2P : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G},
    Hyp24 Ω K K' W S R R' z u →
      Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤

@[expose] def Hyp51VertexP : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K₀ : Subgroup G},
    AscStand Ω K₀ → (∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) →
      ∀ {K K' : Subgroup G} {z x y e₁ e₂ : G}, K ∈ Ω → K' ∈ Ω →
      IsUniqueInvolution K z → IsUniqueInvolution K' z → ∀ {B : Subgroup G}, IsElemAbelian 2 B →
        z ∈ B → x ∈ K → y ∈ K' → x * y ∈ B → x * y ≠ 1 → x * y ≠ z →
        e₁ ∈ B → e₁ ≠ 1 → e₁ ≠ z → e₁ ∈ trivialOnQuot K →
        e₂ ∈ B → e₂ ≠ 1 → e₂ ≠ z → e₂ ∈ trivialOnQuot K' → Hyp51At B z

theorem eq_bot_of_normalizer_eq_top_core {G : Type} [Group G] [Finite G] [CoreLike G]
    {A : Subgroup G} (hodd : Odd (Nat.card A)) (hN : Subgroup.normalizer (A : Set G) = ⊤) :
    A = ⊥ := by
  have hnormal : A.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have h : A ≤ CFSG.oddCore G := le_sSup ⟨hnormal, hodd⟩
  rw [CoreLike.oddCore_eq_bot] at h
  exact le_bot_iff.mp h

theorem eq_one_of_central_core {G : Type} [Group G] [CoreLike G] {c : G}
    (hc : ∀ g : G, g * c = c * g) : c = 1 := by
  have h : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr hc
  rw [CoreLike.center_eq_bot] at h
  exact Subgroup.mem_bot.mp h

end Residuals

end CFSG.ClassicalInvolution.Q8P.P24
