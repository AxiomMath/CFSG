module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I248At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
    ∀ (X K Q : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
      IsChevSimple q (PSimple p K) →
      (∃ A : Subgroup (MulAut (PQuot p K)), IsElemAbelian p A ∧ p ^ 3 ≤ Nat.card A) →
      Q ≤ K → IsPGroup q Q → Nat.card Q = q ^ (Nat.card K).factorization q →
      (3 ≤ CFSG.Open.pRank q Q ∧ K = CFSG.HardMathSupport.Solomon.Coordinator.coreIn q 3 Q K) ∨
        IsU3Case p q K

@[expose] def I267At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
    ∀ (X K B : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPLayer p X = K →
      IsChevSimple q (PSimple p K) → IsElemAbelian p B → B ≤ X →
      p ^ GLATwoLocalRank p ↥X ≤ Nat.card B → p ^ 4 ≤ Nat.card B →
      Nat.card ↥(B ⊓ centModSubgroup p K) = p →
      (∃ B' D J : Subgroup G, IsElemAbelian p B' ∧ B' ≤ X ∧ InD p B' 1 K D J ∧
          (B' = B ∨ (Nat.card B ≤ Nat.card B' ∧ ∃ T : Subgroup G, T ≤ X ∧ T ≠ ⊥ ∧
            IsPGroup 2 T ∧ B' ≤ Subgroup.normalizer (T : Set G))) ∧
          Nat.card ↥(B' ⊓ centModSubgroup p K) = p ∧
          (CFSG.Open.pRank p B < GLATwoLocalRank q ↥X ∨ ∃ T : Subgroup G, T ≤ X ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
            D ≤ Subgroup.normalizer (T : Set G) ∧
            CoversMod p (X ⊓ Subgroup.normalizer (T : Set G)) J)) ∨
      (Nat.card B = p ^ 4 ∧ p = 3 ∧ ∃ Q : TauCeti.PrimePower, Q.p = q ∧
        ((pSimpleIsLie p K (.A 2 Q) ∧ p ∣ Q.card - 1) ∨
          (pSimpleIsLie p K (.twistedA 2 Q) ∧ p ∣ Q.card + 1))) ∨
      (Nat.card B = p ^ 4 ∧ B = (B ⊓ centModSubgroup p K) ⊔ (B ⊓ K) ∧
        (B ⊓ centModSubgroup p K) ⊓ (B ⊓ K) = ⊥ ∧ Subgroup.center (PQuot p K) = ⊥ ∧
        ∃ Q : TauCeti.PrimePower, Q.p = q ∧
          ((pSimpleIsLie p K (.A 3 Q) ∧ p ∣ Q.card - 1) ∨
            (pSimpleIsLie p K (.twistedA 3 Q) ∧ p ∣ Q.card + 1))) ∨
      (Nat.card B = p ^ 4 ∧ B = (B ⊓ centModSubgroup p K) ⊔ (B ⊓ K) ∧
        (B ⊓ centModSubgroup p K) ⊓ (B ⊓ K) = ⊥ ∧ Subgroup.center (PQuot p K) = ⊥ ∧
        ∃ Q : TauCeti.PrimePower, Q.p = q ∧
          (pSimpleIsLie p K (.B 3 Q) ∨ pSimpleIsLie p K (.twistedD 4 Q)) ∧
            p ∣ Q.card ^ 2 - 1) ∨
      ((Nat.card B = p ^ 5 ∨ Nat.card B = p ^ 6) ∧ Nat.card ↥(B ⊓ K) = p ^ 4 ∧
        Subgroup.center (PQuot p K) = ⊥ ∧
        ∃ Q : TauCeti.PrimePower, Q.p = q ∧ pSimpleIsLie p K (.D 4 Q) ∧ p ∣ Q.card ^ 2 - 1)

@[expose] def I71U3At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
    ∀ (X L A : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X L → IsU3Case p q L →
      IsElemAbelian p A → A ≤ Subgroup.normalizer (L : Set G) →
      Nat.card A ≤ p ^ 3 * Nat.card ↥(A ⊓ centModSubgroup p L)

end CFSG.LocalAnalysis.GLTheoremA
