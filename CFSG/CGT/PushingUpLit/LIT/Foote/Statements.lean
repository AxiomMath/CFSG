module

public import CFSG.CGT.PushingUpLit.LIT.Foote.ZSub

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.RankThree.PartOne CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding

@[expose] def TwoOrbit {G : Type} [Group G] (M J : Subgroup G) : Prop :=
  ∃ J' : Subgroup G, J' ≠ J ∧ ∀ m ∈ M, rightConjugate J m = J ∨ rightConjugate J m = J'

@[expose] def FourGroupMeet {G : Type} [Group G] (M J : Subgroup G) : Prop :=
  ∃ h : G, h ∉ M ∧ ∃ W : Subgroup G, W ≤ rightConjugate J h ⊓ Subgroup.normalizer (J : Set G) ∧
    CFSG.Open.IsElemAbelian 2 W ∧ Nat.card W = 4

@[expose] def Lemma54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M J : Subgroup G) (z₀ : G),
    CE G M J → ZData J z₀ → TwoOrbit M J

@[expose] def Lemma55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M J : Subgroup G) (z₀ : G),
    CE G M J → ZData J z₀ → TwoOrbit M J → FourGroupMeet M J

@[expose] def Lemma56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M J : Subgroup G) (z₀ : G),
    CE G M J → ZData J z₀ → TwoOrbit M J → FourGroupMeet M J → False

end CFSG.CGT.PushingUpLit.LIT.Foote
