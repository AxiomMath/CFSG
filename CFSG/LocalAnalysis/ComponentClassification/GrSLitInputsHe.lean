module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def MaximalTwoComponentInputHe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    IsSimpleGroup (GeneralizedFitting.subgroup G) →
    (∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a) →
    ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G) →
    Assembly.KProper Blueprint.Catalog G →
    ∀ J : Subgroup G, GSWeakMaximalComponent J → 2 ≤ pRank 2 ↥J →
    (¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
        Nonempty (J ⧸ Open.fusionZStar J ≃*
          Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K))) →
    IsHeldType (J ⧸ Open.fusionZStar J) →
    ∀ t : G, orderOf t = 2 → J ≤ centralizer ({t} : Set G) →
      (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
          (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ⊔
            J ∧
      (3 ≤ pRank 2 ↥J → ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤
        (pPrimeCore 2 J).map J.subtype ⊓
          (pPrimeCore 2 (conjugate J g)).map (conjugate J g).subtype)

end CFSG.ComponentClassification.GrSLit
