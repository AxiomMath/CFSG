module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def HasTwoLocalWitness (S : Type) [Group S] [Finite S] (r : ℕ) : Prop :=
  ∃ V E : Subgroup S, V ≠ ⊥ ∧ IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set S) ∧
    IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r

@[expose] def isTD4of (r : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .trialityD4 q => q.card = r
    | _ => False

@[expose] def I1432Model {Q : Type} [Group Q] [Finite Q] (K I : Subgroup Q) (y : Q) : Prop :=
  CFSG.Open.IsQuasisimple (PQuot 3 K) ∧ IsCatalogGroup (PSimple 3 K) ∧
    y ∈ Subgroup.normalizer (K : Set Q) ∧ y ^ 3 = 1 ∧
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Q)) I ∧ ¬ K ≤ I ⊔ GLAPPrimeCoreOf 3 K

@[expose] def I1432ClsD4 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I : Subgroup Q) (y : Q), I1432Model K I y →
    S8.IsTypeWithCenter 3 I (S8.isD4of 3) 1 →
      catalogIs (PSimple 3 K) (S8.sporIs .Fi24Prime) ∨ catalogIs (PSimple 3 K) (S8.isD4of 27)

@[expose] def I1432ClsG2 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I : Subgroup Q) (y : Q), I1432Model K I y →
    S8.IsTypeWithCenter 3 I (S8.isG2of 3) 1 →
      catalogIs (PSimple 3 K) (S8.sporIs .Th) ∨ catalogIs (PSimple 3 K) (S8.sporIs .Fi24Prime) ∨
        catalogIs (PSimple 3 K) (S8.isG2of 27) ∨ catalogIs (PSimple 3 K) (S8.isD4of 3) ∨
        catalogIs (PSimple 3 K) (isTD4of 3) ∨ catalogIs (PSimple 3 K) (S8.isD4of 27)

@[expose] def I1432WitD4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S (S8.isD4of 27) → HasTwoLocalWitness S 12

@[expose] def I1432WitG2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    catalogIs S (S8.isG2of 27) ∨ catalogIs S (S8.isD4of 3) ∨ catalogIs S (isTD4of 3) →
      HasTwoLocalWitness S 4

@[expose] def I1432WitFi24 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    catalogIs (Y ⧸ Subgroup.center Y) (S8.sporIs .Fi24Prime) → HasTwoLocalWitness Y 5

@[expose] def I1432Cent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    (∀ z ∈ Subgroup.center Y, ∃ n : ℕ, z ^ 3 ^ n = 1) →
    (catalogIs (Y ⧸ Subgroup.center Y) (S8.isD4of 27) ∨ catalogIs (Y ⧸ Subgroup.center Y) (S8.isG2of 27) ∨
      catalogIs (Y ⧸ Subgroup.center Y) (S8.isD4of 3) ∨ catalogIs (Y ⧸ Subgroup.center Y) (isTD4of 3)) →
    Nat.card (Subgroup.center Y) = 1

@[expose] def I1432BD4 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I B : Subgroup Q) (y : Q), I1432Model K I y →
    S8.IsTypeWithCenter 3 I (S8.isD4of 3) 1 → catalogIs (PSimple 3 K) (S8.isD4of 27) →
    IsElemAbelian 3 B → B ≤ Subgroup.normalizer (K : Set Q) → y ∈ B →
    Nat.card B ≤ 3 ^ 9 * Nat.card ↥(B ⊓ centModSubgroup 3 K)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
