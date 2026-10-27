module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open

variable {X : Type} [Group X] [Finite X]

@[expose] def Bender46 (G T S : Subgroup X) : Prop :=
  ∃ n : ℕ,
    conjugateClosure G T = pCoreOf 2 (conjugateClosure G T) ⊔ ⁅T, G⁆ ∧
    pCoreOf 2 (conjugateClosure G T) ⊓ ⁅T, G⁆ = ⊥ ∧
    ⁅pCoreOf 2 (conjugateClosure G T), ⁅T, G⁆⁆ = ⊥ ∧
    IsElemAbelian 2 (pCoreOf 2 (conjugateClosure G T)) ∧
    Nat.card (pCoreOf 2 (conjugateClosure G T)) = 2 ^ n ∧
    IsBenderType ⁅T, G⁆ n ∧
    IsElemAbelian 2 T ∧ Nat.card T = 2 ^ n ∧
    relativeWeakClosure G T S ⊓ G ≤ ⁅T, G⁆ ∧
    T ⊓ pCoreOf 2 (conjugateClosure G T) = ⊥

@[expose] def Concl46 (G T S : Subgroup X) : Prop :=
  pRank 2 T = 1 ∨
  G ⊔ T ≤ Subgroup.normalizer (relativeWeakClosure G T S : Set X) ∨
  Bender46 G T S

@[expose] def IH46 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (G T S Q H : Subgroup Y) (g : Y),
    Nat.card (G ⊔ T : Subgroup Y) < n →
    SylowFrame G T S → Hyp43 G T Q H → T ≠ ⊥ → CFSG.oddCore G = ⊥ → g ∈ G →
    relativeWeakClosure G T S = T ⊔ rightConjugate T g →
    rightConjugate T g ≤ Subgroup.normalizer (T : Set Y) →
    Concl46 G T S

omit [Finite X] in
theorem Bender46.lemma46 {G T S : Subgroup X} (h : Bender46 G T S) :
    ∃ n : ℕ,
      conjugateClosure G T = pCoreOf 2 (conjugateClosure G T) ⊔ ⁅T, G⁆ ∧
      pCoreOf 2 (conjugateClosure G T) ⊓ ⁅T, G⁆ = ⊥ ∧
      ⁅pCoreOf 2 (conjugateClosure G T), ⁅T, G⁆⁆ = ⊥ ∧
      IsElemAbelian 2 (pCoreOf 2 (conjugateClosure G T)) ∧
      Nat.card (pCoreOf 2 (conjugateClosure G T)) = 2 ^ n ∧
      IsBenderType ⁅T, G⁆ n := by
  obtain ⟨n, h1, h2, h3, h4, h5, h6, -⟩ := h
  exact ⟨n, h1, h2, h3, h4, h5, h6⟩

end CFSG.ComponentClassification.AschbacherTheorem3
