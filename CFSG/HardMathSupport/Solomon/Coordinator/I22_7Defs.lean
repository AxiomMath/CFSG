module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

@[expose] noncomputable def oThreeIn {K : Type*} [Group K] (W : Subgroup K) : Subgroup K :=
  sSup {N : Subgroup K | N ≤ W ∧ N.Normal ∧ IsPGroup 3 N}

@[expose] def NoCompIn {K : Type*} [Group K] (W : Subgroup K) : Prop :=
  ∀ J : Subgroup K, J ≤ W → IsSubnormal J ⊤ → ¬ CFSG.Open.IsQuasisimple ↥J

structure FiCoverK (K : Type) [Group K] [Finite K] : Prop where
  kgroup : CFSG.Open.IsKGroup K
  perfect : commutator K = ⊤
  layer : GLAPLayer 5 (⊤ : Subgroup K) = ⊤
  fi : IsFiTwentyTwo (K ⧸ GLAPPrimeCore 5 K)

@[expose] def I22_7Coprime : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (N : Subgroup K) [N.Normal], Nat.Coprime 3 (Nat.card N) →
    ∀ P : Subgroup K, IsPGroup 3 P → 3 ≤ CFSG.Open.pRank 3 P →
      (⊤ : Subgroup (K ⧸ N)) ≤ weakCoreIn 3 (P.map (QuotientGroup.mk' N)) ⊤ →
        (⊤ : Subgroup K) ≤ weakCoreIn 3 P ⊤

@[expose] def I22_7Comps : Prop :=
  ∀ (K : Type) [Group K] [Finite K], FiCoverK K → GLAPPrimeCore 3 K = ⊥ →
    ∀ J : Subgroup K, J ≤ ⁅GLAPPrimeCore 5 K, (⊤ : Subgroup K)⁆ → IsSubnormal J ⊤ →
      CFSG.Open.IsQuasisimple ↥J → ∀ P : Subgroup K, IsPGroup 3 P →
        Nat.card P = 3 ^ (Nat.card K).factorization 3 → (⊤ : Subgroup K) ≤ weakCoreIn 3 P ⊤

@[expose] def I22_7Rank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ → GLAPPrimeCore 3 K = ⊥ →
    ∀ (R' W : Subgroup K) [R'.Normal], W = ⁅R', (⊤ : Subgroup K)⁆ → NoCompIn W →
      CFSG.Open.pRank 3 (oThreeIn W) ≤ 2 → W = ⊥

@[expose] def I22_7ThreeRankU : Prop :=
  ∀ (K : Type) [Group K] [Finite K], FiCoverK K → GLAPPrimeCore 3 K = ⊥ →
    ∀ (W : Subgroup K) [W.Normal], W = ⁅GLAPPrimeCore 5 K, (⊤ : Subgroup K)⁆ → NoCompIn W →
      3 ≤ CFSG.Open.pRank 3 (oThreeIn W) → ∀ P : Subgroup K, IsPGroup 3 P →
        Nat.card P = 3 ^ (Nat.card K).factorization 3 →
        (⊤ : Subgroup (K ⧸ W)) ≤ weakCoreIn 3 (P.map (QuotientGroup.mk' W)) ⊤ →
          (⊤ : Subgroup K) ≤ weakCoreIn 3 P ⊤

end CFSG.HardMathSupport.Solomon.Coordinator
