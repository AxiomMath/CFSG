module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank

@[expose] def solomonLStarOf {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  ⨆ (K : Subgroup G) (_ : IsTwoComponentIn K H ∧ IsSolomonMaximal K), K

@[expose] def Thm12Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ∀ N : Subgroup G, IsPLocal 2 N → solomonLStarOf N ≠ ⊥ →
      IsQuasisimple (solomonLStarOf N ⧸ pPrimeCore 2 (solomonLStarOf N)) ∨
      Blueprint.OddLieType (GeneralizedFitting.subgroup G) ∨
      (Odd N.index ∧ ∀ K : Subgroup G, IsTwoComponentIn K N →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
          Nonempty (K ⧸ pPrimeCore 2 K ≃* StatedSp 2 F))

@[expose] def AschbacherRankOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ∀ K : Subgroup G, IsSolomonMaximal K → CFSG.pRank 2 ↥K ≤ 1 →
      Blueprint.OddLieType (GeneralizedFitting.subgroup G)

@[expose] def GSLStarSolomonStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ J : Subgroup G, GrSLit.GSWeakMaximalComponent J → 2 ≤ CFSG.pRank 2 ↥J →
    (¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
        Nonempty (J ⧸ Open.fusionZStar J ≃* StatedProj (StatedSp 2 K))) →
    IsSolomonMaximal J

end CFSG.ComponentClassification.Sol76
