module

public import CFSG.GH74.Generic.BProg.B2.WeakSigGen
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

@[expose] def innJoin {J : Type} [Group J] {A : Type} [Group A] (α : A →* MulAut J) : Subgroup (MulAut J) :=
  (MulAut.conj : J →* MulAut J).range ⊔ α.range

@[expose] def GenLoc4 (J : Type) [Group J] : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (α : A →* MulAut J), IsRank23 A →
    SectionalTwoRankLE ↥(innJoin α) 4 → gammaAct α = ⊤ ∨ (LocE1 α ∧ LocE2 α ∧ LocE3 α)

theorem GenLoc.genLoc4 {J : Type} [Group J] (h : GenLoc J) : GenLoc4 J :=
  fun A _ _ α hA _ => h A α hA

@[expose] def WeakSig2NormG4 (J : Type) [Group J] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], pPrimeCore 2 Y = ⊥ → SectionalTwoRankLE Y 4 →
    ∀ L : Subgroup Y, IsComponent L → Nonempty (↥L ≃* J) → ∀ D W : Subgroup Y,
      CFSG.IsElementaryAbelian 2 ↥D → (pRank 2 ↥D = 2 ∨ pRank 2 ↥D = 3) → Odd (Nat.card ↥W) →
      D ≤ normalizer (W : Set Y) →
      (∀ E : Subgroup Y, E ≤ D → pRank 2 ↥D - 1 ≤ pRank 2 ↥E →
        centralizer (E : Set Y) ≤ normalizer (W : Set Y)) →
      D ≤ normalizer (L : Set Y) → W ≤ centralizer (L : Set Y)

@[expose] def WeakSig2TwoG4 (J : Type) [Group J] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], pPrimeCore 2 Y = ⊥ → SectionalTwoRankLE Y 4 →
    ∀ L : Subgroup Y, IsComponent L → Nonempty (↥L ≃* J) → ∀ D W : Subgroup Y,
      CFSG.IsElementaryAbelian 2 ↥D → (pRank 2 ↥D = 2 ∨ pRank 2 ↥D = 3) → Odd (Nat.card ↥W) →
      D ≤ normalizer (W : Set Y) →
      (∀ E : Subgroup Y, E ≤ D → pRank 2 ↥D - 1 ≤ pRank 2 ↥E →
        centralizer (E : Set Y) ≤ normalizer (W : Set Y)) →
      (∃ L' : Subgroup Y, ∀ d ∈ D, conjugate L d = L ∨ conjugate L d = L') →
      W ≤ centralizer (L : Set Y)

end CFSG.GH74.Generic.BProg.B2
