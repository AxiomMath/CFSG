module

public import CFSG.CGT.PushingUpLit.T2K.Global
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.GH74.Defs

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Assembly
open scoped commutatorElement

@[expose] def IsTightlyEmbedded {G : Type} [Group G] (X : Subgroup G) : Prop :=
  Even (Nat.card ↥X) ∧ CFSG.Open.classicalInvolutionTightlyEmbedded X

theorem isTightlyEmbedded_iff_tightlyEmbedded {G : Type} [Group G] (X : Subgroup G) :
    IsTightlyEmbedded X ↔ ComponentClassification.AschbacherTightEmbedding.TightlyEmbedded X :=
  (ComponentClassification.AschbacherTightEmbedding.tightlyEmbedded_iff_classical X).symm

@[expose] def SolomonTimmesfeldTight : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M : Subgroup G) (n : ℕ), T2Hyp G L M n →
    M ≤ Subgroup.normalizer (L : Set G) → IsTightlyEmbedded (Subgroup.centralizer (L : Set G)) →
    Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) = M →
      (∃ s : G, orderOf s = 4 ∧ Subgroup.centralizer (L : Set G) = Subgroup.zpowers s) ∨
        ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 R (Subgroup.centralizer (L : Set G)) ∧
          (R.subgroupOf (Subgroup.centralizer (L : Set G))).Normal ∧ CFSG.Open.IsElemAbelian 2 R

@[expose] def Aschbacher78One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M : Subgroup G) (n : ℕ), T2Hyp G L M n →
    M ≤ Subgroup.normalizer (L : Set G) → ∀ T : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 2 T M →
        Subgroup.normalizer (T : Set G) ≤ M ∨ CFSG.GH74.SectionalTwoRankLE G 4

end CFSG.CGT.PushingUpLit.T2K
