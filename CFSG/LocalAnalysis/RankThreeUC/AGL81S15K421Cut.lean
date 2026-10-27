module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup

@[expose] def K421DataLin : Prop :=
  ∀ (S : Type) [Group S] [Finite S], (IsLinTwo 6 S ∨ IsLinTwo 7 S) → Data421 S 7

@[expose] def K421NonTransLin : Prop :=
  ∀ (S : Type) [Group S] [Finite S], (IsLinTwo 6 S ∨ IsLinTwo 7 S) →
    ∀ E : Subgroup S, IsElemAbelian 3 E → Nat.card E = 9 → ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧
      ∀ φ : MulAut S, E.map φ.toMonoidHom = E → φ a ≠ b

@[expose] def K421DataSp : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → 5 ≤ p →
    IsSpSix (fun Q => p ∣ Q + 1) S → Data421 S p

@[expose] def K421DataOm : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → 5 ≤ p →
    IsOmegaEightMinus (fun Q => p ∣ Q + 1) S → Data421 S p

@[expose] def K421Data : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → 5 ≤ p → Bad1517 p S → Data421 S p

theorem K421Data_of_parts (hL : K421DataLin) (hS : K421DataSp) (hO : K421DataOm) : K421Data := by
  intro S _ _ p hp hp5 hbad
  rcases hbad with ⟨hlin, rfl⟩ | hsp | hom
  · exact hL S hlin
  · exact hS S p hp hp5 hsp
  · exact hO S p hp hp5 hom

end CFSG.LocalAnalysis.RankThreeUC.S15
