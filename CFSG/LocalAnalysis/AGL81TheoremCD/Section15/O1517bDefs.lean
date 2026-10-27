module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

structure O1517bRed (X : Type) [Group X] [Finite X] (p : ℕ) (P A Y : Subgroup X) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections X
  core : CFSG.pPrimeCore 3 X = ⊥
  layer_ne : CFSG.layer X ≠ ⊥
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤
  rank : CFSG.Open.pRank 3 P = 3
  shape : (CFSG.Open.IsElemAbelian 3 P ∧ Nat.card P = 27) ∨
    IsCyclic ↥(Subgroup.center ↥P)
  card_A : Nat.card A = 3
  normal_A : A.Normal
  le_P : A ≤ P
  strong : CFSG.RankThree.PartOne.IsStronglyPEmbedded p Y
  le_Y : P ≤ Y
  gamma : CFSG.Open.rankThreeGamma 2 3 P ≤ Y

@[expose] def KFactE9AutTwoThree : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
    ∀ X₀ P₀ Y₀ : Subgroup (MulAut L), (MulAut.conj : L →* MulAut L).range ≤ X₀ →
      CFSG.AGLEmbedding.CatalogSimpleSections ↥X₀ → CFSG.ABGLocalTools.IsSylowOf 3 P₀ X₀ →
      CFSG.Open.IsElemAbelian 3 P₀ → Nat.card P₀ = 9 → Y₀ ≤ X₀ →
      (∀ D : Subgroup (MulAut L), D ≤ P₀ → D ≠ ⊥ →
        X₀ ⊓ Subgroup.normalizer (D : Set (MulAut L)) ≤ Y₀) →
      ¬ (MulAut.conj : L →* MulAut L).range ≤ Y₀ →
      ∀ r : ℕ, r.Prime → r ∣ Nat.card Y₀ → r = 2 ∨ r = 3

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
