module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15

abbrev NineTwelveKerConclusion (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G)
    (p : ℕ) : Prop :=
  (¬ pLayerIn p H ≤ M → ∀ L : Subgroup G, IsPComponentIn p L (kSub p M H) →
    IsTwoPrimeComponentIn L H ∨
      (p = 3 ∧ Nonempty (↥L ⧸ CFSG.solvableRadical ↥L ≃* alternatingGroup (Fin 6)))) ∧
  (pLayerIn p H ≤ M → ∀ R : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf 3 R (relPPrimeCore p H) →
    kSub p M H = (kSub p M H ⊓ Subgroup.centralizer (R : Set G)) ⊔ relPPrimeCore p (kSub p M H) ∨
    (p = 13 ∧
      kSub p M H = (kSub p M H ⊓ Subgroup.centralizer (R : Set G)) ⊔ kerIn M (kSub p M H)) ∨
    (p = 5 ∧ CFSG.IsExtraspecialPGroup 3 ↥(omegaOnePSub 3 R) ∧
      Nat.card ↥(omegaOnePSub 3 R) = 3 ^ 5 ∧ Monoid.exponent ↥(omegaOnePSub 3 R) = 3))

@[expose] def NineTwelveKerGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M →
    NineTwelveKerConclusion G M Q H E p

@[expose] def NineTwelveThirteenRankThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G),
    NineSettingGen G M 13 Q H E 2 → H ∈ H2Fam M Q → 13 ∉ sigmaM G M → pLayerIn 13 H ≤ M →
    CFSG.Open.pRank 13 H = 3 →
    ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R (relPPrimeCore 13 H) →
      (∃ y ∈ kSub 13 M H, y ∈ Subgroup.normalizer (R : Set G) ∧ (∃ n : ℕ, y ^ 13 ^ n = 1) ∧
        y ∉ Subgroup.centralizer (R : Set G)) →
      kSub 13 M H = (kSub 13 M H ⊓ Subgroup.centralizer (R : Set G)) ⊔ kerIn M (kSub 13 M H)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
