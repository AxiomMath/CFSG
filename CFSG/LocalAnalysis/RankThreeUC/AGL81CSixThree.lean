module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PCoreQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open scoped MatrixGroups
open scoped commutatorElement

@[expose] def SixThreeOneList (p : ℕ) (Y : Type) [Group Y] : Prop :=
  (IsSLType 2 (ZMod p) Y ∨ IsSLType 3 (ZMod p) Y ∨ IsPSLType 2 (ZMod p) Y ∨ Nat.card Y = 1) ∨
  (p = 7 ∧ IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 7)))
    (fun B _ => Nat.card B = 2) Y) ∨
  (p = 5 ∧
    (IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
        (fun B _ => Nat.card B = 2) Y ∨
      IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
        (fun B _ => IsQ8D8Type B) Y ∨
      IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) Y)) ∨
  (p = 3 ∧
    (IsSLType 2 (ZMod 5) Y ∨
      IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
        (fun B _ => IsQ8D8Type B) Y ∨
      IsExtNotation (fun A _ => Nat.card A = 3) (fun B _ => Nat.card B = 13) Y ∨
      ∃ W : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3)), oPPrimeHull 3 W = W ∧
        Nonempty (Y ≃* ↥W ⧸ CFSG.pCore 3 ↥W)))

@[expose] def SixThreeOne : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X],
    Subgroup.centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X →
    CFSG.Open.pRank p (CFSG.pCore p X) ≤ 3 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3 →
    SixThreeOneList p ↥(oPPrimeHull p (⊤ : Subgroup (X ⧸ CFSG.pCore p X)))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
