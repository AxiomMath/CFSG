module

public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open scoped commutatorElement

@[expose] def IsLTwoEight (S : Type*) [Group S] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 8 ∧ Nonempty (S ≃* StatedSL 2 F)

@[expose] def AutLTwoEightBalance : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsLTwoEight S →
    ∀ A : Subgroup (MulAut S), IsElemAbelian 3 A → 3 ^ 2 ≤ Nat.card A →
      ∀ T : Subgroup (MulAut S), Nat.Coprime 3 (Nat.card T) →
        A ≤ Subgroup.normalizer (T : Set (MulAut S)) → T = ⊥

@[expose] def fixSubAut {S : Type*} [Group S] (C : Subgroup (MulAut S)) : Subgroup S :=
  ⨅ (c : MulAut S) (_ : c ∈ C), MonoidHom.eqLocus c.toMonoidHom (MonoidHom.id S)

@[expose] def L2FieldPlane : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (IsLTwoTwentySeven S ∨ (IsLTwoOddPow S ∧ ¬ IsLTwoEight S)) →
    ∀ A : Subgroup (MulAut S), IsElemAbelian 3 A → ¬ A ≤ innerAut S →
      Nat.card A ≤ 9 ∧ (Nat.card A = 9 →
        ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ a₂ ∉ Subgroup.zpowers a₁ ∧
          fixSubAut (Subgroup.zpowers a₁) ⊔ fixSubAut (Subgroup.zpowers a₂) = ⊤)

@[expose] def NNL2OddPow : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) → IsLTwoOddPow ↥K →
      I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K ∨ I271CaseC K B

@[expose] def NNHatMTwentyTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) → IsHatMTwentyTwo ↥K →
      I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K ∨ I271CaseC K B

@[expose] def NNSLThreeExc : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) → IsSLThreeExc ↥K →
      I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K ∨ I271CaseC K B

@[expose] def NNSUThreeExc : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) → IsSUThreeExc ↥K →
      I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K ∨ I271CaseC K B

end CFSG.HardMathSupport.Solomon.Coordinator
