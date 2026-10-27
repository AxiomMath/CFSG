module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def Harris82Theorem3Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup ↥(Open.genFittingFStar G) →
    ∀ W : Subgroup G, (∀ a ∈ W, a * a = 1) → Nat.card W = 4 →
    ∀ (L : Subgroup G) (p : ℕ), p.Prime → p ≠ 2 → IsTwoComponentIn L (centralizer (W : Set G)) →
      IsMTypeSchur p ↥L → L ⊓ W ≠ ⊥ → ∀ w ∈ L ⊓ W, w ≠ 1 →
        IsTwoComponentIn (GSThmB.conjClosure L (GSThmB.layerIn (centralizer {w})))
            (centralizer {w}) ∨
          IsSimpleChevalleyOver p ↥(Open.genFittingFStar G)

@[expose] def Harris81Lemma35IdentFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ w v : G, orderOf w = 2 → v * v = 1 → v ∉ zpowers w →
    v ∈ centralizer {w} →
    ∀ L : Subgroup G, IsTwoComponentIn L (centralizer {w} ⊓ centralizer {v}) →
      IsMTypeSchur p ↥L → ∀ k : ℕ, 1 ≤ k → 5 ≤ p ^ k → IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L) →
      w ∈ L →
    ∀ K : Subgroup G, K = GSThmB.conjClosure L (GSThmB.layerIn (centralizer {w})) → L ≤ K →
      IsTwoComponentIn K (centralizer {w}) → w ∈ K → ¬ IsMTypeSchur p ↥K →
      K.map (MulAut.conj v).toMonoidHom = K →
        L = GSThmB.layerIn (K ⊓ centralizer {v}) ∧
        ((p = 7 ∧ IsSLTwoOver 7 (↥L ⧸ pPrimeCore 2 ↥L) ∧
            IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
            Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 16 ∧
            GrSLit.IsL34Type ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))) ∨
          (p = 5 ∧ IsSLTwoOver 5 (↥L ⧸ pPrimeCore 2 ↥L) ∧ ∃ n : ℕ, 4 ≤ n ∧
            IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
            Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
            Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
              alternatingGroup (Fin (2 * n + 1)))) ∨
          (p = 3 ∧ IsSLTwoOver 9 (↥L ⧸ pPrimeCore 2 ↥L) ∧ ∃ n : ℕ, 4 ≤ n ∧
            IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) ∧
            Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 ∧
            Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃*
              alternatingGroup (Fin (2 * n)))))

end CFSG.ComponentClassification.HarrisLit
