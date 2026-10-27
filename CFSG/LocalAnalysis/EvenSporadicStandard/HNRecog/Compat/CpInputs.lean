module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

@[expose] def Cover4A : Prop :=
  ∀ {G : Type} [Group G] {a z : G}, F5Std a z → ∀ y ∈ orb4A a z a,
    ∀ d ∈ orb2A a a ∩ orb2A a y, ∀ t ∈ InvIn (Gxy a y),
      ∃ r ∈ InvIn (Gxyz a d y), ConjIn (Gxy a y) r t

@[expose] def Wit4A : Prop :=
  ∀ {G : Type} [Group G] {a z : G}, F5Std a z → ∀ x ∈ orb4A a z a,
    ∀ d ∈ orb2A a a ∩ orb2A a x, ∀ t ∈ InvIn (Gxyz a d x), t ≠ d →
      ∃ y ∈ Gxy t d, IsConj a y ∧ y ∉ Gx a ∧ y ∉ orb4A a z a ∧ y ∉ orb5A a a ∧ y ∉ orb5E a a

@[expose] def Gen5A : Prop :=
  ∀ {G : Type} [Group G] {a z : G}, F5Std a z → ∀ x ∈ orb5A a a,
    ∃ t t' : G, t ∈ InvIn (Gxy a x) ∧ t' ∈ InvIn (Gxy a x) ∧ t ≠ t' ∧ t * t' = t' * t ∧
      Subgroup.closure ((Gxyz a t x : Set G) ∪ (Gxyz a t' x : Set G)) = Gxy a x

@[expose] def Wit5E : Prop :=
  ∀ {G : Type} [Group G] {a z : G}, F5Std a z → ∀ x ∈ orb5E a a, ∀ t t' : G, IsConj a t →
    IsConj z t' → IsConj z (t * t') → t ∈ Gxy a x → t' ∈ Gxy a x → t * t' = t' * t →
      x ∈ Subgroup.closure {y | y ∈ Gxy t t' ∧ IsConj a y ∧ y ∉ orb5E a a}

@[expose] def Wit20 : Prop :=
  ∀ {G : Type} [Group G] {a z : G}, F5Std a z → ∀ b ∈ orb2A a a, ∀ t ∈ InvIn (Gxy a b),
    t ≠ a → t ≠ b → t ≠ a * b → ∃ w, IsConj a w ∧ w ∈ Gxy b t ∧ w ∉ Gx a

@[expose] def Gen2A : Prop :=
  ∀ {G : Type} [Group G] {a z : G}, F5Std a z → ∀ x, IsConj a x → ∀ b ∈ orb2A a x,
    ∃ c₁ c₂ g : G, c₁ ∈ InvIn (Gxy x b) ∧ c₂ ∈ InvIn (Gxy x b) ∧ c₁ ≠ x ∧ c₁ ≠ b ∧
      c₁ ≠ x * b ∧ c₂ ≠ x ∧ c₂ ≠ b ∧ c₂ ≠ x * b ∧ g ∈ Gxyz x c₁ c₂ ∧ b * g ≠ g * b ∧
      Subgroup.closure ((Gxy x c₁ : Set G) ∪ (Gxy x c₂ : Set G)) = Gx x

structure CompatOpen : Prop where
  cover4A : Cover4A
  wit4A : Wit4A
  gen5A : Gen5A
  wit5e : Wit5E
  wit20 : Wit20
  gen2A : Gen2A

end CFSG.EvenSporadicStandard.HNRecog.Section4
