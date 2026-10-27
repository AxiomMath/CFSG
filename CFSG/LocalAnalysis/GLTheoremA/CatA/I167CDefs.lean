module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)

@[expose] def PFreeCover (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    Nonempty (X ⧸ Subgroup.center X ≃* S) → ¬ p ∣ Nat.card (Subgroup.center X)

@[expose] def HalfSplitLab (p : ℕ) (labK : GLALabel) : Prop :=
  ∃ labH : GLALabel, CFSG.StandardType.GGLabelIso labH labK ∧ GLAHalfSplit16 p labH True

@[expose] def ScpS (p : ℕ) (S : Type) [Group S] (Bb : Subgroup (MulAut S)) : Prop :=
  ∀ s : S, (∀ β ∈ Bb, β s = s) → s ^ p = 1 → (MulAut.conj s : MulAut S) ∈ Bb

@[expose] def CentJ {S : Type} [Group S] (Bb : Subgroup (MulAut S)) (α : MulAut S) (J : Subgroup S) : Prop :=
  ∀ β ∈ Bb, (∀ j ∈ J, β j = j) → β ∈ Subgroup.zpowers α

@[expose] def Type167S (p : ℕ) (S : Type) [Group S] (J : Subgroup S) : Prop :=
  (p = 3 ∧ ∃ n : ℕ, Odd n ∧ catalogIs (PSimple 3 J) (isLnA n 2) ∧
      (catalogIs S (isLnA (n + 2) 2) ∨ catalogIs S (isLnA n 8))) ∨
  (p = 3 ∧ ∃ n : ℕ, Even n ∧ catalogIs (PSimple 3 J) (isOmMA n 2) ∧
      (catalogIs S (isOmPA (n + 1) 2) ∨ catalogIs S (isOmMA n 8))) ∨
  (∃ n k : ℕ, Odd n ∧ 1 ≤ k ∧ p ∣ 2 ^ k + 1 ∧ catalogIs (PSimple p J) (isOmPA n (2 ^ k)) ∧
      (catalogIs S (isOmMA (n + 1) (2 ^ k)) ∨ catalogIs S (isOmPA n (2 ^ (p * k))) ∨
        (p = 5 ∧ n = 3 ∧ k = 2 ∧ catalogIs S (isLnA 6 4))))

@[expose] def I167CAt (Fam : GLALabel → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ) (Bb : Subgroup (MulAut S)) (α : MulAut S)
    (J : Subgroup S) (labK : GLALabel),
    p.Prime → p ≠ 2 → Fam labK → Subgroup.center S = ⊥ → IsElemAbelian p Bb → α ∈ Bb → orderOf α = p →
      InnDiagKind S labK α → (PFreeCover p S → ScpS p S Bb) → CentJ Bb α J → HalfSplitLab p labK →
        GLAPComponent p (fixSubgroup α) J → Type167J p J → Type167S p S J

@[expose] def I167CLin : Prop := I167CAt Y10GField.FamLin

@[expose] def I167CUni : Prop := I167CAt Y10GField.FamUni

@[expose] def I167CSymp : Prop := I167CAt Y10GField.FamSymp

@[expose] def I167COrth : Prop := I167CAt Y10GField.FamOrth

end CFSG.LocalAnalysis.GLTheoremA.I167

end
