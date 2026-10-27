module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUPairComp

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.ComponentClassification.Burgoyne.U CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank Matrix

@[expose] def kaUBar {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}
    (A : uU h n) (c : K) : Prop :=
  ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
    ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = c • 1

@[expose] def KAUSplit : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p f K) (n : ℕ)
    (hn : 3 ≤ n), p ≠ 2 → ∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ →
      (J.card = 2 ∨ J.card + 2 = n → 5 ≤ p ^ f) →
      KAAll (uConjAut h (by omega) (uSign h J))

@[expose] def KAU4SplitThree : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p f K), p ≠ 2 →
    p ^ f = 3 → ∀ J : Finset (Fin 4), J.card = 2 →
      KAAll (uConjAut h (by norm_num) (uSign h J))

@[expose] def KAU4Pair : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p f K) (_ : p ≠ 2)
    (h2 : (2 : K) ≠ 0) (l : K) (hl : l ≠ 0) (hN : h.norm l = -1),
      KAAll (uConjAut h (n := 2 + 2) (by norm_num) (uPairA (m := 2) h h2 hl hN))

@[expose] def KAUGOrth : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p f K) (n : ℕ)
    (hn : 3 ≤ n), p ≠ 2 → ¬ (p ^ f = 3 ∧ n ≤ 4) → ∀ A : uU h n, kaUBar h A 1 →
      KAAll (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h))

@[expose] def KAU4GOrthThree : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p f K), p ≠ 2 →
    p ^ f = 3 → ∀ A : uU h 4, kaUBar h A 1 →
      KAAll (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) (barEq h))

@[expose] def KAU4GSp : Prop :=
  ∀ (p f : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p f K), p ≠ 2 →
    ∀ A : uU h 4, kaUBar h A (-1) →
      KAAll (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) (barEq h))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
