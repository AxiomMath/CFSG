module

public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

@[expose] def IVK_3_1f_lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    Prop21g z S

@[expose] def IVK_3_3_lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    Prop21h z

@[expose] def IVK_8_5_lift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, H ≠ ⊤ → Prop32Concl H

@[expose] def Leaf_Lemma26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    Lemma26 z S

@[expose] def Leaf_Prop27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx0 G z k S →
    ∀ (x : G) (T : Subgroup G), Prop27Hyp z x T → Prop27Concl z k S x T

@[expose] def Leaf_Lemma29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    Lemma29 z k

@[expose] def Leaf_Lemma31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H J R : Subgroup G, H ≠ ⊤ → Lemma31Hyp k H J R → Lemma31Concl z H J R

@[expose] def Leaf_Prop34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, Cen z ≤ H → H ≠ ⊤ → Prop34Concl z k S H

@[expose] def Leaf_Lemma35 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H J R : Subgroup G, Cen z ≤ H → H ≠ ⊤ → Lemma35Hyp H J R → Lemma35Concl z k S H J R

structure Stage2Bg : Prop where
  ivk_3_1f : IVK_3_1f_lift
  ivk_3_3 : IVK_3_3_lift
  ivk_8_5 : IVK_8_5_lift
  lemma26 : Leaf_Lemma26
  prop27 : Leaf_Prop27
  lemma29 : Leaf_Lemma29
  lemma31 : Leaf_Lemma31
  prop34 : Leaf_Prop34
  lemma35 : Leaf_Lemma35

end CFSG.GH74.GLS.Stage2.Local
