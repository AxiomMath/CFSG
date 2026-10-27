module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KxDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie IsChevSimple)
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection KxSection IsParabolicTwo
  IsReeIndex IsRankTwoOddIndex)

@[expose] def IsLTwoIndex : TauCeti.LieTypeIndex → Prop
  | .A 1 q => q.p ≠ 2
  | _ => False

@[expose] def IsLThreeUThreeIndex : TauCeti.LieTypeIndex → Prop
  | .A 2 q => q.p ≠ 2
  | .twistedA 2 q => q.p ≠ 2
  | _ => False

@[expose] def KFact2713Three : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L R : Subgroup A) (z : A),
    catalogIs ↥L (onLie (fun i => IsLTwoIndex i ∧ i.characteristic ≠ 3)) → z ∈ L →
    orderOf z = 3 → R ≤ L → IsPGroup 2 R → z ∈ normalizer (R : Set A) →
    (∃ y ∈ R, z * y ≠ y * z) →
    Nonempty (↥L ≃* PSL(3, ZMod 2)) ∨
      ∀ J : Subgroup A, normalizer (zpowers z : Set A) ⊓ L ≤ J → R ≤ J → L ≤ J

@[expose] def KFactL3U3SL2Three : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A) (z : A),
    catalogIs ↥L (onLie (fun i => IsLThreeUThreeIndex i ∧ i.characteristic ≠ 3)) →
    CFSG.Open.pRank 3 L ≤ 1 → z ∈ L → orderOf z = 3 →
    ∃ K₀ N : Subgroup A, K₀ ≤ L ∧ z ∈ K₀ ∧ z ∉ N ∧ S622IsSimpleSection K₀ N ∧ N ≠ ⊥ ∧
      IsPGroup 2 N ∧ K₀ ≤ centralizer (N : Set A)

@[expose] def KFactParabolicSectionThree : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K K₀ : Subgroup A) (z : A),
    IsChevSimple 2 ↥K → CFSG.Open.pRank 3 K ≤ 1 → ¬ Nonempty (↥K ≃* PSL(3, ZMod 2)) → orderOf z = 3 →
    z ∈ K₀ →
    IsParabolicTwo A K K₀ → K₀ ≠ K →
    (∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ → ¬ U ≤ rankThreePrimeCore 3 K₀) →
    KxSection z K₀ 3

@[expose] def KFactJ1ClosureThree : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L J : Subgroup A) (z : A),
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) → z ∈ L → orderOf z = 3 →
    normalizer (zpowers z : Set A) ⊓ L ≤ J →
    (∀ U : Subgroup A, U ≤ J → U ≤ L → U ≠ ⊥ → IsPGroup 2 U → z ∈ normalizer (U : Set A) →
      normalizer (U : Set A) ⊓ L ≤ J) → L ≤ J

@[expose] def KFactThreeRankTwo : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A) (d : TauCeti.ValidLieTypeIndex),
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    (d.1.characteristic = 3 ∨ IsReeIndex d.1 ∨ IsRankTwoOddIndex d.1) →
    2 ≤ CFSG.Open.pRank 3 L

@[expose] def P622L27Exit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (T S L : Subgroup G), P622KxCfg 3 P M x z T S L →
    rankThreePrimeCore 3 (centralizer ({x} : Set G)) = ⊥ → Nonempty (↥L ≃* PSL(3, ZMod 2)) →
    SmallRankCaseOne x T

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
