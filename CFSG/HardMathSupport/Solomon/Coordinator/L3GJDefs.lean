module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns

@[expose] def Lemma510iiLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      IsUpsilonComponent B b L → IsExtremalType (barOf 3 L) →
      ∀ (y : G) (hy : y ∈ L), y ∈ B → y ≠ 1 →
        HasOrderThreeLift (barOf 3 L) (QuotientGroup.mk (⟨y, hy⟩ : ↥L))

end CFSG.HardMathSupport.Solomon.Coordinator
