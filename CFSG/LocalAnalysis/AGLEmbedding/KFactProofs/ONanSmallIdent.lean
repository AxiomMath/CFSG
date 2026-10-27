module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def IsTitsGroup (K : Type) [Group K] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, d.1 = .tits ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsSporadicGroup (s : TauCeti.SporadicName) (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group)

@[expose] def IsSmallStrongP (p : ℕ) (K : Type) [Group K] : Prop :=
  IsSmallLinTwo p K ∨ IsSmallUnitary p K ∨ IsAltTwoP p K ∨
    (p = 3 ∧ (IsLinThreeFour K ∨ IsSporadicGroup .M11 K)) ∨
    (p = 5 ∧ (IsTitsGroup K ∨ IsSporadicGroup .McL K ∨ IsFi22 K)) ∨
    (p = 11 ∧ IsSporadicGroup .J4 K)

@[expose] def KFactSmallIdent : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      pRank p (⊤ : Subgroup K) ≤ 2 → IsSmallStrongP p K

end CFSG.AGLEmbedding
