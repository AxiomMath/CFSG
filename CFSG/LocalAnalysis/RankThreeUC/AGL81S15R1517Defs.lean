module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup

@[expose] def Bad1517 (p : ℕ) (S : Type) [Group S] : Prop :=
  ((IsLinTwo 6 S ∨ IsLinTwo 7 S) ∧ p = 7) ∨
    IsSpSix (fun Q => p ∣ Q + 1) S ∨ IsOmegaEightMinus (fun Q => p ∣ Q + 1) S

@[expose] def BadIdx1517 (p : ℕ) : TauCeti.LieTypeIndex → Prop
  | .B 3 Q => Q.p = 2 ∧ p ∣ Q.card + 1
  | .twistedD 4 Q => Q.p = 2 ∧ p ∣ Q.card + 1
  | .A 5 Q => Q.card = 2 ∧ p = 7
  | .A 6 Q => Q.card = 2 ∧ p = 7
  | _ => False

section YDefs

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def CaseA1517 (p : ℕ) (D : Subgroup Y) : Prop :=
  Nat.card D = 3 ∧ 2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (D : Set Y)) ∧
    ¬ CFSG.HallHigman.IsPSolvable p ↥(Subgroup.centralizer (D : Set Y))

@[expose] def SylowShape1517 (D : Subgroup Y) : Prop :=
  ∀ P : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (D : Set Y)) →
    ((IsElemAbelian 3 P ∧ Nat.card P = 27) ∨ IsCyclic ↥(Subgroup.center ↥P)) ∧
      3 ≤ CFSG.Open.pRank 3 P

@[expose] def NonTrans1517 (E : Subgroup Y) : Prop :=
  ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ ∀ g ∈ Subgroup.normalizer (E : Set Y), g * a * g⁻¹ ≠ b

structure Out1517 (Y : Type) [Group Y] [Finite Y] (p : ℕ) : Prop where
  dvd : ∀ D : Subgroup Y, Nat.card D = 3 → p ∣ Nat.card (Subgroup.centralizer (D : Set Y))
  caseA : ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E = 9 → ∃ D ≤ E, CaseA1517 p D
  shape : ∀ D : Subgroup Y, Nat.card D = 3 → ¬ CaseA1517 p D → SylowShape1517 D

end YDefs

structure Data421 (S : Type) [Group S] [Finite S] (p : ℕ) : Prop where
  each : ∀ D : Subgroup S, Nat.card D = 3 →
    (2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (D : Set S)) +
        (3 - CFSG.Open.pRank p (⊤ : Subgroup S)) ∧
      ¬ CFSG.HallHigman.IsPSolvable p ↥(Subgroup.centralizer (D : Set S))) ∨
    (SylowShape1517 D ∧ 1 ≤ CFSG.Open.pRank p (Subgroup.centralizer (D : Set S)) +
        (3 - CFSG.Open.pRank p (⊤ : Subgroup S)))
  caseA : ∀ E : Subgroup S, IsElemAbelian 3 E → Nat.card E = 9 → ∃ D ≤ E, Nat.card D = 3 ∧
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (D : Set S)) +
        (3 - CFSG.Open.pRank p (⊤ : Subgroup S)) ∧
      ¬ CFSG.HallHigman.IsPSolvable p ↥(Subgroup.centralizer (D : Set S))

@[expose] def OutTwoGroup (S : Type) [Group S] : Prop :=
  ∀ φ : MulAut S, ∃ k : ℕ, φ ^ (2 ^ k) ∈ (MulAut.conj : S →* MulAut S).range

@[expose] def Row1520One (G : Type) [Group G] [Finite G] (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M) :
    Prop :=
  ∀ p ∈ sigmaM G M, 5 ≤ p → ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
    GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
      ∃ I : Subgroup ↥M, I ≤ cMHat L ∧ CFSG.IsPComponent p (I.subgroupOf (cMHat L)) ∧
        CFSG.Open.pRank p I = 1 ∧ 1 ≤ CFSG.Open.pRank 3 I

end CFSG.LocalAnalysis.RankThreeUC.S15
