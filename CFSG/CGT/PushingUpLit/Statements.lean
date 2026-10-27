module

public import CFSG.CGT.PushingUpLit.Defs
public import CFSG.CGT.PushingUp.Inputs
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open scoped Pointwise

@[expose] def AschbacherFactorizationTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ T : Sylow 2 G, characteristicCoreStar (T : Subgroup G) ≠ ⊤ →
      CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (characteristicCoreStar (T : Subgroup G)) ∨
        ∃ X : Subgroup G, InClassXG X

@[expose] def AschbacherFactorizationThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ X : Subgroup G, IsMaximalInClassXG X →
      ∃ M : Subgroup G, maximalTwoLocalsContaining (X : Set G) = {M} ∧
        (X.subgroupOf M).IsSubnormal

@[expose] def AschbacherTheoremOneK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ X : Subgroup G, InOmega X → (∀ Y : Subgroup G, InOmega Y → Arrow X Y → Y = X) →
      ∃ M : Subgroup G, maximalTwoLocalsContaining (X : Set G) = {M}

@[expose] def AschbacherTheoremTwoK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    CFSG.Assembly.IsCharTwoType G →
    ∀ (L M : Subgroup G), InClassX ↥L → IsMaximalTwoLocal M → L ≤ M →
      (L.subgroupOf M).IsSubnormal → maximalTwoLocalsContaining (L : Set G) = {M} →
        ∀ n : ℕ, 2 ≤ n → IsNaturalSLTwoModule ↥L n →
          Nonempty (G ≃* projSL 3 (GaloisField 2 n)) ∨
            Nonempty (G ≃* projSp 2 (GaloisField 2 n)) ∨
              (n = 2 ∧ CFSG.GH74.sectionalTwoRank G = 4)

@[expose] def SolomonAlternatingBlockK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    CFSG.Assembly.IsCharTwoType G →
    ∀ (M X : Subgroup G), IsMaximalTwoLocal M → X ≤ M → (X.subgroupOf M).IsSubnormal →
      InClassX ↥X → (∃ n : ℕ, 1 ≤ n ∧ IsNaturalAltModule ↥X n) →
        maximalTwoLocalsContaining (X : Set G) = {M} → CFSG.GH74.SectionalTwoRankLE G 4

theorem AschbacherTheoremOne.toK (h : AschbacherTheoremOne) : AschbacherTheoremOneK :=
  fun G _ _ _ hchar => h G hchar

theorem AschbacherTheoremTwo.toK (h : AschbacherTheoremTwo) : AschbacherTheoremTwoK :=
  fun G _ _ _ hs hchar => h G hs hchar

theorem SolomonAlternatingBlock.toK (h : SolomonAlternatingBlock) : SolomonAlternatingBlockK :=
  fun G _ _ _ hs hchar => h G hs hchar

end CFSG.CGT.PushingUpLit
