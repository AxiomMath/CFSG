module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG CFSG.RankThree.PartTwo
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM InClassXBlock NineThreeTwo NineThreeThree
  NineThreeFour IsClassicalTwoOrG2 IsOrthogonalTwo HasIrreducibleCommutatorQuotient blockV)
open CFSG.QuasithinUnique (IsShort2)

section Defs

variable {G : Type} [Group G]

@[expose] def SStarOrderTwo (S L : Subgroup G) : Prop :=
  ∃ s ∈ S, S ≤ Subgroup.zpowers s ⊔ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ∧
    s ^ 2 ∈ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ∧
    s ∉ L ⊔ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G)

@[expose] def TransvectionData (S L : Subgroup G) : Prop :=
  ∃ s ∈ S, S ≤ Subgroup.zpowers s ⊔ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ∧
    s ∉ L ⊔ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ∧
    Nat.card ↥⁅blockV S L, Subgroup.zpowers s⁆ = 2

end Defs

@[expose] def EightNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
      NineThreeTwo X S L ∨ InClassXBlock L ∨ SStarOrderTwo S L

@[expose] def EightEightTransvection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
      SStarOrderTwo S L → TransvectionData S L

@[expose] def OrthOrTripleA6 {G : Type} [Group G] (X L : Subgroup G) : Prop :=
  IsOrthogonalTwo ↥(barM X L) ∨
    (Nat.card (Subgroup.center ↥(barM X L)) = 3 ∧
      Nonempty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃* alternatingGroup (Fin 6)))

@[expose] def EightEightShort : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L →
    IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) →
      TransvectionData S L → HasIrreducibleCommutatorQuotient L (blockV S L) →
        (IsOrthogonalTwo ↥(barM X L) → IsShort2 L ∧ IsTypeScriptL L) ∧
        ((Nat.card (Subgroup.center ↥(barM X L)) = 3 ∧
            Nonempty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃*
              alternatingGroup (Fin 6))) →
          NineThreeFour X S L ∧ IsA6Z3Type L)

end CFSG.HardMathSupport.Cooperstein.StructureLie
