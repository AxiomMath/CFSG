module

public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def E186QuotOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ (N : Subgroup G) [N.Normal], Odd (Nat.card N) → N ≤ H → N = ⊥

@[expose] def E186QuotCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ (N : Subgroup G) [N.Normal], N ≤ Subgroup.center G → IsPGroup 2 N → N ≤ H →
        (∀ J ∈ Ω, J ⊓ N = ⊥) → N = ⊥

end CFSG.ClassicalInvolution.Asc77
