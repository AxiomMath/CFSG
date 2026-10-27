module

public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Open.StatedDefs
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Quasithin.Background.B1Restrict

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

@[expose] def IsU4Group (n : ℕ) {S : Type} [CommGroup S] (L : Subgroup (MulAut S)) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = n ∧ d.1 = .twistedA 3 q) ∧
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsIrrOn {S : Type} [CommGroup S] (X : Subgroup (MulAut S)) : Prop :=
  ∀ W : Subgroup S, (∀ x ∈ X, ∀ w ∈ W, x w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def NaturalU4Mod (n : ℕ) {S : Type} [CommGroup S] (L : Subgroup (MulAut S)) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    ∃ (ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F)) (ψ : S ≃* Multiplicative (Fin 4 → F)),
      ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec
          (Multiplicative.toAdd (ψ s)))) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
    ∃ (ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
      (ψ : S ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
      ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
          (Multiplicative.toAdd (ψ s))))

@[expose] def U4FFNatural : Prop :=
  ∀ (S : Type) [CommGroup S] [Finite S], (∀ s : S, s ^ 2 = 1) →
  ∀ (n : ℕ) (L A : Subgroup (MulAut S)),
    IsU4Group n L → IsElemAbelian2 A → A ≤ Subgroup.normalizer (L : Set (MulAut S)) →
    (∃ a ∈ A, ∃ l ∈ L, a * l ≠ l * a) → IsIrrOn (L ⊔ A) →
    Nat.card S ≤ Nat.card A * Nat.card (fixV A) →
    IsIrrOn L ∧ NaturalU4Mod n L

end CFSG.LocalAnalysis.RankThreeUC
