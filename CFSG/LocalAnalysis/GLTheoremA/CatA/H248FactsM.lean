module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def L227FactM : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (G : Type) [Group G] [Finite G] (K Q : Subgroup G), CFSG.Open.IsKGroup ↥K →
      GLAPLayer p K = K →
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.GLAPPrimeCore p ↥K) →
      IsSimpleGroup (↥K ⧸ M227 p K) → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥K ⧸ M227 p K)) →
      Q ≤ K → IsPGroup q Q → Nat.card Q = q ^ (Nat.card K).factorization q →
      4 ≤ CFSG.Open.pRank q ((Q.subgroupOf K).map (QuotientGroup.mk' (W227 p K))) →
      4 ≤ CFSG.Open.pRank q ((Q.subgroupOf K).map (QuotientGroup.mk' (M227 p K))) →
      CFSG.HardMathSupport.Solomon.Coordinator.coreIn q 3
          ((Q.subgroupOf K).map (QuotientGroup.mk' (W227 p K))) ⊤ = ⊤ →
      CFSG.HardMathSupport.Solomon.Coordinator.coreIn q 3 Q K = K

end CFSG.LocalAnalysis.GLTheoremA.H248
