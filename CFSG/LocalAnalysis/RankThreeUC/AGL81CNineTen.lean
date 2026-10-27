module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThree
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15

abbrev StarGroup {G : Type} [Group G] (p : ℕ) (H : Subgroup G) : Type :=
  ↥H ⧸ primeComplementCore (G := ↥H) p

noncomputable abbrev KStarQuot {G : Type} [Group G] (p : ℕ) (M H : Subgroup G) : Type :=
  ↥(kStar p M H) ⧸ CFSG.pCore p ↥(kStar p M H)

@[expose] def NineTenThreeCorrected {G : Type} [Group G] [Finite G] (p : ℕ) (M H : Subgroup G) :
    Prop :=
  SixThreeOneList p (KStarQuot p M H) ∧ Nat.card (KStarQuot p M H) ≠ 1

abbrev QuotKer {G : Type} [Group G] (M H : Subgroup G) : Type :=
  ↥H ⧸ Subgroup.normalCore ((M ⊓ H).subgroupOf H)

noncomputable def cStarL {G : Type} [Group G] (p : ℕ) (H : Subgroup G) :
    Subgroup (StarGroup p H) :=
  Subgroup.centralizer (starImg p H (pLayerIn p H) : Set (StarGroup p H))

abbrev NineTenConclusion (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G)
    (p : ℕ) : Prop :=
  (¬ pLayerIn p H ≤ M →
    (xSub p M H ≤ M ∧ H = kSub p M H ⊔ (H ⊓ M) ∧ ((kSub p M H).subgroupOf H).Normal) ∨
    (p = 3 ∧
      (IsPSLType 2 (GaloisField 2 3) ↥(kStar p M H) ∨
        IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 6)))
          (fun B _ => Nat.card B = 3) ↥(kStar p M H) ∨
        IsSLType 3 (GaloisField 2 2) ↥(kStar p M H)) ∧
      CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) = 2 ∧
      ¬ xSub p M H ≤ M ∧ CFSG.HallHigman.IsPSolvable p ↥(xSub p M H))) ∧
  (pLayerIn p H ≠ ⊥ → pLayerIn p H ≤ M →
    (p = 3 ∧
      (∃ S : Set (Subgroup G), S.ncard = 3 ∧
        (∀ J ∈ S, IsPComponentIn p J H ∧ CFSG.Open.pRank p J = 1) ∧ pLayerIn p H = sSup S ∧
        ∀ J ∈ S, ∀ J' ∈ S, ∃ e ∈ E, J' = J.map (MulAut.conj e).toMonoidHom) ∧
      CFSG.pCore p (StarGroup p H) = ⊥ ∧
      IsPSLType 2 (ZMod 3) ↥(oPPrimeHull p (⊤ : Subgroup (QuotKer M H)))) ∨
    (3 < p ∧ CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) = 2 ∧
      CFSG.Open.pRank p (pLayerIn p H) = 1 ∧
      oPPrimeHull p (⊤ : Subgroup (StarGroup p H)) =
        starImg p H (pLayerIn p H) ⊔ oPPrimeHull p (cStarL p H) ∧
      IsExtNotation (fun A _ => IsSLType 2 (ZMod p) A) (fun B _ => IsHomocyclicRank2 p B)
        ↥(oPPrimeHull p (cStarL p H))) ∨
    (p = 3 ∧ CFSG.Open.pRank p (starImg p H (pLayerIn p H)) ≤ 2 ∧
      CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) = 2 ∧
      CFSG.IsQuasisimple ↥(starImg p H (pLayerIn p H)) ∧
      IsPSLType 2 (ZMod 3) ↥(oPPrimeHull p (⊤ : Subgroup (QuotKer M H))))) ∧
  (pLayerIn p H = ⊥ → NineTenThreeCorrected p M H)

@[expose] def NineTen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSetting G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M →
    NineTenConclusion G M Q H E p

@[expose] def NineTenGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M →
    NineTenConclusion G M Q H E p

abbrev NineTwelveConclusion (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G)
    (p : ℕ) : Prop :=
  (¬ pLayerIn p H ≤ M → ∀ L : Subgroup G, IsPComponentIn p L (kSub p M H) →
    IsTwoPrimeComponentIn L H ∨
      (p = 3 ∧ Nonempty (↥L ⧸ CFSG.solvableRadical ↥L ≃* alternatingGroup (Fin 6)))) ∧
  (pLayerIn p H ≤ M → ∀ R : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf 3 R (relPPrimeCore p H) →
    kSub p M H = (kSub p M H ⊓ Subgroup.centralizer (R : Set G)) ⊔ relPPrimeCore p (kSub p M H) ∨
    (p = 13 ∧ IsElemAbelian 3 (omegaOnePSub 3 R) ∧ Nat.card ↥(omegaOnePSub 3 R) = 27 ∧
      p ∉ sigmaM G M ∧
      kSub p M H = (kSub p M H ⊓ Subgroup.centralizer (R : Set G)) ⊔ kerIn M (kSub p M H) ∧
      ∃ N : Subgroup (StarGroup p H), N ≤ starImg p H (kerIn M (kSub p M H)) ∧
        (N.subgroupOf (starImg p H (kerIn M (kSub p M H)))).Normal ∧
        IsSLType 3 (ZMod 3) ↥N) ∨
    (p = 5 ∧ CFSG.IsExtraspecialPGroup 3 ↥(omegaOnePSub 3 R) ∧
      Nat.card ↥(omegaOnePSub 3 R) = 3 ^ 5 ∧ Monoid.exponent ↥(omegaOnePSub 3 R) = 3))

@[expose] def NineTwelve : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSetting G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M →
    NineTwelveConclusion G M Q H E p

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
