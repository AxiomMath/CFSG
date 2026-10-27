module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis.RankThreeUC CFSG.Open CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

@[expose] def wedgeIdx : Fin 6 → Fin 4 × Fin 4 := ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

@[expose] def comp2 {A : Type*} [CommRing A] (g : Matrix (Fin 4) (Fin 4) A) :
    Matrix (Fin 6) (Fin 6) A :=
  Matrix.of fun a b =>
    g (wedgeIdx a).1 (wedgeIdx b).1 * g (wedgeIdx a).2 (wedgeIdx b).2 -
      g (wedgeIdx a).1 (wedgeIdx b).2 * g (wedgeIdx a).2 (wedgeIdx b).1

@[expose] def NaturalOmega6 (n : ℕ) {S : Type} [CommGroup S] (L : Subgroup (MulAut S)) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
    (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
    ∃ (ε : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
      (ψ : S ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
      ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
        (((ε l : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
          (Multiplicative.toAdd (ψ s)))

theorem NaturalOmega6.naturalU4Mod {n : ℕ} {S : Type} [CommGroup S] {L : Subgroup (MulAut S)}
    (h : NaturalOmega6 n L) : NaturalU4Mod n L :=
  Or.inr h

end CFSG.HardMathSupport.U4FF
