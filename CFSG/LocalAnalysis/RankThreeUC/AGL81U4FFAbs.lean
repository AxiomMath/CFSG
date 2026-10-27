module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

structure U4OffenderData (n : ℕ) {V : Type} [CommGroup V] (L A : Subgroup (MulAut V)) : Prop where
  isU4 : IsU4Group n L
  elemAbelian : IsElemAbelian2 A
  normalizes : A ≤ Subgroup.normalizer (L : Set (MulAut V))
  noncomm : ∃ a ∈ A, ∃ l ∈ L, a * l ≠ l * a
  offender : ∀ Y : Subgroup V, A ≤ stabSub Y →
    Nat.card Y ≤ (A ⊓ centSub Y).relIndex A * Nat.card ↥(Y ⊓ fixV A)

@[expose] def NaturalU4Abstract (n : ℕ) {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    ∃ (ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F)) (φ : ↥(commV L) →* Multiplicative (Fin 4 → F)),
      Function.Surjective φ ∧ φ.ker = (fixV L).subgroupOf (commV L) ∧
      ∀ (l : ↥L) (u u' : ↥(commV L)), (l : MulAut V) (u : V) = (u' : V) →
        φ u' = Multiplicative.ofAdd
          (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec
            (Multiplicative.toAdd (φ u)))) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
    ∃ (ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
      (φ : ↥(commV L) →* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
      Function.Surjective φ ∧ φ.ker = (fixV L).subgroupOf (commV L) ∧
      ∀ (l : ↥L) (u u' : ↥(commV L)), (l : MulAut V) (u : V) = (u' : V) →
        φ u' = Multiplicative.ofAdd
          (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
            Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
            (Multiplicative.toAdd (φ u))))

@[expose] def PartAAbstract : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (n : ℕ) (L A : Subgroup (MulAut V)), U4OffenderData n L A → NaturalU4Abstract n L

end CFSG.LocalAnalysis.RankThreeUC
