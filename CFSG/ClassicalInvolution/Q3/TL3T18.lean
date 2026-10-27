module

public import CFSG.ClassicalInvolution.Q3.TL3T17
public import CFSG.ClassicalInvolution.Q3.TL3T13
public import CFSG.ClassicalInvolution.Q3.TL3T16

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

@[expose] def ThmDGen (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaGen Ω →
    (∀ J ∈ Ω, IsPGroup 2 J) → (∀ J ∈ Ω, Nat.card J = 2 ^ r) →
    (∀ J ∈ Ω, AEmpty Ω J) →
    ∀ P : Set (Subgroup G), P ⊆ Ω →
    (∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L') →
    (∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) →
    classicalInvolutionOddCore ↥(pSpan P) = ⊥ →
    (∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q) →
    (∀ L ∈ P, ∀ L' ∈ P, L = L') ∨
      (∃ W : Subgroup G, WIn P (pSpan P) = {W}) ∨ (∃ E : Subgroup G, E8Struct (pSpan P) E) ∨
      Nonempty (AEIdentOn P 7 AE.e64Sets AE.e64Sub) ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (AEIdent P n)) ∨
      Nonempty (AEIdentOn P 8 AE.e29Sets AE.e29Sub)

theorem tightThmD3_of_gen (hD : ThmDGen 3) : TightThmD3 := by
  intro G _ _ Ω hΩ h2 h8 _ hA hnt P hPΩ htrans hinv hodd hE2 hthin
  by_cases hPne : P.Nonempty
  swap
  · exact Or.inl fun L hL => absurd ⟨L, hL⟩ hPne
  rcases hD G Ω hΩ h2 (fun J hJ => by rw [h8 J hJ]; norm_num) hA P hPΩ htrans hinv hodd hE2 with
    hsing | ⟨W, hW⟩ | ⟨E, hE⟩ | h64 | hAE | h29
  · exact Or.inl fun L hL L' hL' hne => absurd (hsing L hL L' hL') hne
  · exact (false_of_WIn_eq hΩ h2 h8 hPΩ hPne hinv hthin hW).elim
  · exact Or.inl (indep_of_e8Struct hΩ h2 h8 hnt hPΩ hE2 hE)
  · exact Or.inr (Or.inr (Or.inl h64))
  · exact Or.inr (Or.inl hAE)
  · exact Or.inr (Or.inr (Or.inr h29))

end CFSG.ClassicalInvolution.Q3.TC.Thin
