module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

structure ParityFacts (a z : G) : Prop where
  even_of_not_conj : ∀ x t : G, IsConj a x → orderOf t = 2 → t ∈ Gxy a x →
    ¬ IsConj (a * t) (x * t) → Even (orderOf (a * x))
  two_power_of_2AB : ∀ x t : G, IsConj a x → t ∈ orb2AB a z a → t ∈ Gxy a x →
    ∃ k : ℕ, orderOf (a * x) = 2 ^ k

@[expose] def sBase (a b : G) : Set G :=
  {c | IsConj a c ∧ IsConj a (b * c) ∧ c ≠ a ∧ c ≠ a * b}

@[expose] def sSet (a z b : G) : Fin 6 → Set G :=
  ![{c | c ∈ sBase a b ∧ IsConj a (a * c)},
    {c | c ∈ sBase a b ∧ IsConj z (a * c)},
    {c | c ∈ sBase a b ∧ (a * c) ^ 2 = b},
    {c | c ∈ sBase a b ∧ IsConj z ((a * c) ^ 2)},
    {c | c ∈ sBase a b ∧ orderOf (a * c) = 3},
    {c | c ∈ sBase a b ∧ (a * c) ^ 3 = b}]

structure TableIVFacts (a z : G) : Prop where
  card : ∀ b ∈ orb2A a a, Nat.card ↥(sBase a b) = 2198
  partition : ∀ b ∈ orb2A a a, IsOrbitPartition (Gxy a b) (sBase a b) (sSet a z b)
  card_stab : ∀ b ∈ orb2A a a, StabCard (Gxy a b) (sSet a z b) ![768, 768, 1440, 64, 240, 240]
  shape_4B : ∀ b ∈ orb2A a a, ∀ c ∈ sSet a z b 2, IsShapeZ2TimesSym 6 ↥(Gxyz a b c)
  shape_3A : ∀ b ∈ orb2A a a, ∀ c ∈ sSet a z b 4, IsShapeZ2TimesSym 5 ↥(Gxyz a b c)
  shape_6A : ∀ b ∈ orb2A a a, ∀ c ∈ sSet a z b 5, IsShapeZ2TimesSym 5 ↥(Gxyz a b c)
  s8_4B : ∀ b ∈ orb2A a a, ∀ c ∈ sSet a z b 2,
    Nonempty (↥(derivedOf (Gxy a b) ⊔ Subgroup.zpowers c) ≃* Sym 8)

structure PerpFacts (a z : G) : Prop where
  perp_4B_6A : ∀ b ∈ orb2A a a, ∀ c : G, (c ∈ sSet a z b 2 ∨ c ∈ sSet a z b 5) →
    orb2A a a ∩ orb2A a c = {y | y ∈ centerOf (Subgroup.closure {a, c}) ∧ y ≠ 1}
  class_4A : ∀ b ∈ orb2A a a, ∀ c ∈ sSet a z b 3, IsConjOrbit (Gxy a c) (orb2A a a ∩ orb2A a c)
  cent_4A : ∀ b ∈ orb2A a a, ∀ c ∈ sSet a z b 3, ∀ x ∈ orb2A a a ∩ orb2A a c,
    IsPGroup 2 ↥(Gxyz a x c) ∧ Nat.card ↥(Gxyz a x c) = 2 ^ 6
  pcore_4A : ∀ b ∈ orb2A a a, ∀ c ∈ sSet a z b 3, ∀ x ∈ orb2A a a ∩ orb2A a c,
    x ∈ CFSG.Open.pCoreOf 2 (Gxy a c)
  class_3A : ∀ b ∈ orb2A a a, ∀ c ∈ sSet a z b 4, IsConjOrbit (Gxy a c) (orb2A a a ∩ orb2A a c)
  shape_3A : ∀ b ∈ orb2A a a, ∀ c ∈ sSet a z b 4, ∀ x ∈ orb2A a a ∩ orb2A a c,
    IsShapeZ2TimesSym 5 ↥(Gxyz a x c)

@[expose] def tab5Base (a : G) : Set G := {c | IsConj a c ∧ Even (orderOf (a * c))}

@[expose] def tab5Set (a z : G) : Fin 5 → Set G :=
  ![orb2A a a, orb2B a z a, orb4A a z a, orb4B a a, orb6A a a]

structure TableVFacts (a z : G) : Prop where
  partition : IsOrbitPartition (Gx a) (tab5Base a) (tab5Set a z)
  card_stab : StabCard (Gx a) (tab5Set a z) ![80640, 30720, 640, 1440, 240]
  shape_2A : ∀ c ∈ orb2A a a, IsShapeTwoTwoTimesA8 ↥(Gxy a c)
  shape_2B : ∀ c ∈ orb2B a z a, IsShapeTwoTwoSixS5 ↥(Gxy a c)
  shape_4A : ∀ c ∈ orb4A a z a, IsShapeTwoOneSixByFive ↥(Gxy a c)
  shape_4B : ∀ c ∈ orb4B a a, IsShapeZ2TimesSym 6 ↥(Gxy a c)
  shape_6A : ∀ c ∈ orb6A a a, IsShapeZ2TimesSym 5 ↥(Gxy a c)

@[expose] def fourBSet (a z x : G) : Fin 7 → Set G :=
  ![{(a * x) ^ 2},
    orb2B a z a ∩ orb2B a z x,
    orb2BB a z a ∩ orb2BB a z x,
    orb2A a a ∩ orb2B a z x,
    orb2AB a z a ∩ orb2BB a z x,
    orb2A a x ∩ orb2B a z a,
    orb2AB a z x ∩ orb2BB a z a]

structure FourBFacts (a z : G) : Prop where
  classes : ∀ x ∈ orb4B a a,
    IsOrbitPartition (Gxy a x) {t | t ∈ Gxy a x ∧ orderOf t = 2} (fourBSet a z x)
  case_i : ∀ x ∈ orb4B a a, ∀ t ∈ orb2B a z a ∩ orb2B a z x,
    t * (a * x) ^ 2 ∈ orb2BB a z a ∩ orb2BB a z x ∧
      Gxyz a t x = Gxyz a (t * (a * x) ^ 2) x ∧ IsShapeTwoTwoTimesD8 ↥(Gxyz a t x)
  case_ii : ∀ x ∈ orb4B a a, ∀ t ∈ orb2AB a z a ∩ orb2BB a z x,
    t * (a * x) ^ 2 ∈ orb2A a a ∩ orb2B a z x ∧
      Gxyz a t x = Gxyz a (t * (a * x) ^ 2) x ∧ IsShapeTwoTwoTimesS4 ↥(Gxyz a t x)
  case_iii : ∀ x ∈ orb4B a a, ∀ t ∈ orb2AB a z x ∩ orb2BB a z a,
    t * (a * x) ^ 2 ∈ orb2A a x ∩ orb2B a z a ∧
      Gxyz a t x = Gxyz a (t * (a * x) ^ 2) x ∧ IsShapeTwoTwoTimesS4 ↥(Gxyz a t x)

@[expose] def s7Set (a z x : G) : Fin 3 → Set G :=
  ![orb2A a a ∩ orb2A a x, orb2B a z a ∩ orb2B a z x, orb2BB a z a ∩ orb2BB a z x]

structure S7Facts (a z : G) : Prop where
  orbit : IsConjOrbit (Gx a) (orb3A a a)
  shape : ∀ x ∈ orb3A a a, IsShapeSym 7 ↥(Gxy a x)
  classes : ∀ x ∈ orb3A a a,
    IsOrbitPartition (Gxy a x) {t | t ∈ Gxy a x ∧ orderOf t = 2} (s7Set a z x)
  shape_i : ∀ x ∈ orb3A a a, ∀ t ∈ orb2A a a ∩ orb2A a x, IsShapeZ2TimesSym 5 ↥(Gxyz a t x)
  shape_ii : ∀ x ∈ orb3A a a, ∀ t ∈ orb2B a z a ∩ orb2B a z x, IsShapeD8TimesS3 ↥(Gxyz a t x)
  shape_iii : ∀ x ∈ orb3A a a, ∀ t ∈ orb2BB a z a ∩ orb2BB a z x, IsShapeZ2WrS3 ↥(Gxyz a t x)
  cycleType : ∀ x ∈ orb3A a a, ∀ φ : ↥(Gxy a x) ≃* Sym 7, ∀ t : ↥(Gxy a x),
    ((t : G) ∈ orb2A a a ∩ orb2A a x → (φ t).cycleType = {2}) ∧
      ((t : G) ∈ orb2B a z a ∩ orb2B a z x → (φ t).cycleType = {2, 2}) ∧
      ((t : G) ∈ orb2BB a z a ∩ orb2BB a z x → (φ t).cycleType = {2, 2, 2})

@[expose] def sixASet (a z x : G) : Fin 5 → Set G :=
  ![{(a * x) ^ 3},
    orb2B a z a ∩ orb2B a z x,
    orb2BB a z a ∩ orb2BB a z x,
    orb2A a a ∩ orb2B a z x,
    orb2B a z a ∩ orb2A a x]

structure SixAFacts (a z : G) : Prop where
  classes : ∀ x ∈ orb6A a a,
    IsOrbitPartition (Gxy a x) {t | t ∈ Gxy a x ∧ orderOf t = 2} (sixASet a z x)
  case_i : ∀ x ∈ orb6A a a, ∀ t ∈ orb2B a z a ∩ orb2B a z x,
    t * (a * x) ^ 3 ∈ orb2BB a z a ∩ orb2BB a z x ∧
      Gxyz a t x = Gxyz a (t * (a * x) ^ 3) x ∧ IsShapeZ2TimesD8 ↥(Gxyz a t x)
  case_ii : ∀ x ∈ orb6A a a, ∀ t ∈ orb2A a a ∩ orb2B a z x,
    t * (a * x) ^ 3 ∈ orb2B a z a ∩ orb2A a x ∧
      Gxyz a t x = Gxyz a (t * (a * x) ^ 3) x ∧ IsShapeTwoTwoTimesS3 ↥(Gxyz a t x)

@[expose] def tBase (a z b : G) : Set G := {c | IsConj a c ∧ IsConj z (b * c) ∧ c ≠ a}

@[expose] def tSet (a z b : G) : Fin 8 → Set G :=
  ![{c | c ∈ tBase a z b ∧ IsConj a (a * c)},
    {c | c ∈ tBase a z b ∧ IsConj z (a * c)},
    {c | c ∈ tBase a z b ∧ orderOf (a * c) = 3},
    {c | c ∈ tBase a z b ∧ orderOf (a * c) = 4 ∧ IsConj z ((a * c) ^ 2)},
    {c | c ∈ tBase a z b ∧ orderOf (a * c) = 4 ∧ IsConj a ((a * c) ^ 2)},
    {c | c ∈ tBase a z b ∧ orderOf (a * c) = 5 ∧ IsShapeCentralizerFiveC ↥(Gxy b (a * c))},
    {c | c ∈ tBase a z b ∧ orderOf (a * c) = 5 ∧ IsShapeCentralizerFiveB ↥(Gxy b (a * c))},
    {c | c ∈ tBase a z b ∧ orderOf (a * c) = 6 ∧ IsConj a ((a * c) ^ 3)}]

structure TableVIFacts (a z : G) : Prop where
  card : ∀ b ∈ orb2B a z a, Nat.card ↥(tBase a z b) = 5774
  partition : ∀ b ∈ orb2B a z a, IsOrbitPartition (Gxy a b) (tBase a z b) (tSet a z b)
  card_stab : ∀ b ∈ orb2B a z a,
    StabCard (Gxy a b) (tSet a z b) ![384, 1024, 48, 64, 32, 240, 20, 16]
  shape_3A : ∀ b ∈ orb2B a z a, ∀ c ∈ tSet a z b 2, IsShapeD8TimesS3 ↥(Gxyz a b c)
  shape_4B : ∀ b ∈ orb2B a z a, ∀ c ∈ tSet a z b 4, IsShapeTwoTwoTimesD8 ↥(Gxyz a b c)
  shape_5A : ∀ b ∈ orb2B a z a, ∀ c ∈ tSet a z b 5, IsNonsplitDoubleCoverOfS5 ↥(Gxyz a b c)
  shape_5E : ∀ b ∈ orb2B a z a, ∀ c ∈ tSet a z b 6, IsShapeZ2TimesD10 ↥(Gxyz a b c)
  shape_6A : ∀ b ∈ orb2B a z a, ∀ c ∈ tSet a z b 7, IsShapeZ2TimesD8 ↥(Gxyz a b c)
  two_part_5E : ∀ b ∈ orb2B a z a, ∀ c ∈ tSet a z b 6, padicValNat 2 (Nat.card ↥(Gxy a c)) = 2

structure TableVIIFacts (a z : G) : Prop where
  partition : IsOrbitPartition (Gx a) (oddSet a a) ![orb3A a a, orb5A a a, orb5E a a]
  order_three_five : ∀ c ∈ oddSet a a, orderOf (a * c) = 3 ∨ orderOf (a * c) = 5
  card_3A : ∀ c ∈ orb3A a a, Nat.card ↥(Gx a ⊓ Gx c) = 5040
  shape_5A : ∀ c ∈ orb5A a a, IsShapeU35 ↥(Gxy a c)

end CFSG.EvenSporadicStandard.HNRecog.Section3
