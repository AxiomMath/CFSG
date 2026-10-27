module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Extremal
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def Input19_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ B : Subgroup G, IsElemAbelian p B → ∀ k : ℕ,
      1 ≤ k →
      (∀ D : Subgroup G, IsEkIn p k B D → ∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
        GLAPComponent p (Subgroup.centralizer ({b} : Set G)) J →
          ⁅GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G), J⁆ ≤
            GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))) →
      IsBalancedWrt p k B

@[expose] def Input19_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ B : Subgroup G, IsElemAbelian p B → ∀ k : ℕ,
      1 ≤ k →
      (∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
        GLAPComponent p (Subgroup.centralizer ({b} : Set G)) J → IsCompLocallyBalanced p k B J) →
      IsBalancedWrt p k B

@[expose] def Input19_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X →
      IsElemAbelian p B → GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B →
      ∀ L : Subgroup G, GLAPComponent p X L →
        (3 ≤ CFSG.Open.pRank p B → IsCompLocallyBalanced p 3 B L) ∧
        (2 ≤ CFSG.Open.pRank p B → IsCompWeaklyLocallyBalanced p 2 B L) ∧
        (2 ≤ CFSG.Open.pRank p B → IsCompLocallyBalanced p 2 B L ∨
          (p = 5 ∧ IsFiTwentyTwo (barOf 5 L)) ∨
          (p = 3 ∧ IsExtremalType (↥L ⧸ oPrimeP 3 ↥L)) ∨
          (p = 5 ∧
            (∃ (K : Type) (_ : Field K) (_ : Finite K) (q n : ℕ), q = 2 ^ n ∧ n % 4 = 2 ∧
              Nat.card K = q ^ 2 ∧
              Nonempty ((↥L ⧸ oPrimeP 5 ↥L) ≃* StatedProj (StatedSU 5 q K))) ∧
            Odd (Nat.card ↥(X ⊓ Subgroup.centralizer (B : Set G))) ∧
            ∃ B₀ : Subgroup G, B₀ ≤ B ∧ (B₀.subgroupOf B).index = 25 ∧
              CFSG.Open.pRank 5 B < CFSG.Open.pRank 5 (X ⊓ Subgroup.centralizer (B₀ : Set G))))

end CFSG.HardMathSupport.Solomon.LocalBalance
