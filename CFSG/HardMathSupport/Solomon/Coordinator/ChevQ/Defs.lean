module

public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Fam
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Indices
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns

@[expose] def IsLieQuot (Y : Type*) [Group Y] (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, P d.1 ∧
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def Center64 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    GLAPPrimeCore p Y = ⊥ → ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      p ≠ d.1.characteristic → CFSG.Open.pRank p (Subgroup.center Y) ≤ 1

@[expose] def Gen2318 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    CFSG.Open.IsComponentOf K ⊤ → CFSG.Open.IsElemAbelian 3 B →
      B ≤ Subgroup.normalizer (K : Set X) → GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B →
      B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ → IsLieQuot ↥K Gen2318Index →
        5 ≤ CFSG.Open.pRank 3 B ∧ K ≤ gammaPrimeIn 3 4 B K

@[expose] def Bal209Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B → B ≤ Subgroup.normalizer (K : Set X) →
      GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B → IsLieQuot ↥K Bal209TwoIndex →
        IsStronglyBalancedIn 3 B K

@[expose] def Bal209F4Eight : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    CFSG.Open.IsComponentOf K ⊤ → IsSCp 3 ⊤ B → B ≤ Subgroup.normalizer (K : Set X) →
      GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B → IsLieQuot ↥K IsF4EightIndex →
        ¬ InducesInnerIn B K → IsStronglyBalancedIn 3 B K

@[expose] def ChevQOuterFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → I271Norm 3 K B → IsLieQuot ↥K FourIndex → ¬ InducesInnerIn B K →
      I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K

@[expose] def ChevQTwistedE6Four : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → I271Norm 3 K B → IsLieQuot ↥K IsTwistedE6FourIndex →
      I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K

@[expose] def D44OuterRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    IsLieQuot Y IsD4FourIndex → ∀ A : Subgroup (MulAut Y), CFSG.Open.IsElemAbelian 3 A →
      ¬ A ≤ (MulAut.conj : Y →* MulAut Y).range → Nat.card A ≤ 3 ^ 3

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
