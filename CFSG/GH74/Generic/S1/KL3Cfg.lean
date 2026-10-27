module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Uniqueness.Section174Frame
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

@[expose] def KL3Cfg {S : Type} [Group S] (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S) : Prop :=
  Nat.card F = 3 ∧ Nonempty (↥Pb ≃* SL(3, F)) ∧ yb ∈ Pb ∧ orderOf yb = 2 ∧
    Group.IsSolvable ↥(centralizer ({yb} : Set S))

@[expose] def KL3FamL2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    StatedClassicalModel S .PSL 2 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → False

@[expose] def KL3FamL3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    StatedClassicalModel S .PSL 3 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → Nat.card S = 5616

@[expose] def KL3FamU3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    StatedClassicalModel S .PSU 3 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → False

@[expose] def KL3FamPSp4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    StatedClassicalModel S .PSp 2 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → False

@[expose] def KL3FamL4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    p ^ f % 8 ≠ 1 → StatedClassicalModel S .PSL 4 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → p = 3 ∧ f = 1

@[expose] def KL3FamU4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    p ^ f % 8 ≠ 7 → StatedClassicalModel S .PSU 4 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → False

@[expose] def KL3FamL5 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → 1 ≤ f →
    p ^ f % 4 = 3 → StatedClassicalModel S .PSL 5 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → False

@[expose] def KL3FamU5 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → 1 ≤ f →
    p ^ f % 4 = 1 → StatedClassicalModel S .PSU 5 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → False

@[expose] def KL3FamG2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    LieModel S .G2 0 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → p = 3 ∧ f = 1

@[expose] def KL3FamD4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    LieModel S .trialityD4 0 p f →
      ∀ (F : Type) [Field F] [Finite F] (Pb : Subgroup S) (yb : S), KL3Cfg F Pb yb → False

structure KL3Families : Prop where
  l2 : KL3FamL2
  l3 : KL3FamL3
  u3 : KL3FamU3
  sp4 : KL3FamPSp4
  l4 : KL3FamL4
  u4 : KL3FamU4
  l5 : KL3FamL5
  u5 : KL3FamU5
  g2 : KL3FamG2
  d4 : KL3FamD4

end CFSG.GH74.Generic.S1
