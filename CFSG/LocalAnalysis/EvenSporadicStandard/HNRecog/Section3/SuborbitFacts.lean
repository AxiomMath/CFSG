module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Vocabulary

variable {H : Type} [Group H]

@[expose] def HIsA (a z b : H) (x : H) : Prop :=
  IsConj a x ∨ IsConj (a * z) x ∨ IsConj b x

@[expose] def HIsB (z z₁ : H) (x : H) : Prop :=
  IsConj z x ∨ IsConj z₁ x

@[expose] def A8Dict (z b : H) : Prop :=
  ∀ φ : alternatingGroup (Fin 8) ≃* ↥(derivedOf (Gx b)), ∀ t : alternatingGroup (Fin 8),
    (t : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} → IsConj z (φ t : H)

@[expose] def tab4Base (a b y : H) : Set H :=
  {c | IsConj b c ∧ c ≠ y ∧ c ≠ a * y}

@[expose] def tab4Set (a z b z₁ y : H) : Fin 6 → Set H :=
  ![{c | c ∈ tab4Base a b y ∧ HIsA a z b (y * c)},
    {c | c ∈ tab4Base a b y ∧ HIsB z z₁ (y * c)},
    {c | c ∈ tab4Base a b y ∧ (y * c) ^ 2 = a},
    {c | c ∈ tab4Base a b y ∧ HIsB z z₁ ((y * c) ^ 2)},
    {c | c ∈ tab4Base a b y ∧ orderOf (y * c) = 3},
    {c | c ∈ tab4Base a b y ∧ (y * c) ^ 3 = a}]

structure TableIVData (a z b z₁ y : H) : Prop where
  partition : IsOrbitPartition (Gx y) (tab4Base a b y) (tab4Set a z b z₁ y)
  card_stab : StabCard (Gx y) (tab4Set a z b z₁ y) ![768, 768, 1440, 64, 240, 240]
  shape_4B : ∀ c ∈ tab4Set a z b z₁ y 2, IsShapeZ2TimesSym 6 ↥(Gx y ⊓ Gx c)
  shape_3A : ∀ c ∈ tab4Set a z b z₁ y 4, IsShapeZ2TimesSym 5 ↥(Gx y ⊓ Gx c)
  shape_6A : ∀ c ∈ tab4Set a z b z₁ y 5, IsShapeZ2TimesSym 5 ↥(Gx y ⊓ Gx c)

@[expose] def tab6Base (a z y : H) : Set H :=
  {c | IsConj (a * z) c ∧ c ≠ y}

@[expose] def tab6Set (a z b z₁ y : H) : Fin 8 → Set H :=
  ![{c | c ∈ tab6Base a z y ∧ HIsA a z b (y * c)},
    {c | c ∈ tab6Base a z y ∧ HIsB z z₁ (y * c)},
    {c | c ∈ tab6Base a z y ∧ orderOf (y * c) = 3},
    {c | c ∈ tab6Base a z y ∧ orderOf (y * c) = 4 ∧ HIsB z z₁ ((y * c) ^ 2)},
    {c | c ∈ tab6Base a z y ∧ orderOf (y * c) = 4 ∧ HIsA a z b ((y * c) ^ 2)},
    {c | c ∈ tab6Base a z y ∧ orderOf (y * c) = 5 ∧ IsShapeCentralizerFiveC ↥(Gx (y * c))},
    {c | c ∈ tab6Base a z y ∧ orderOf (y * c) = 5 ∧ IsShapeCentralizerFiveB ↥(Gx (y * c))},
    {c | c ∈ tab6Base a z y ∧ orderOf (y * c) = 6 ∧ HIsA a z b ((y * c) ^ 3)}]

structure TableVIData (a z b z₁ y : H) : Prop where
  partition : IsOrbitPartition (Gx y) (tab6Base a z y) (tab6Set a z b z₁ y)
  card_stab : StabCard (Gx y) (tab6Set a z b z₁ y) ![384, 1024, 48, 64, 32, 240, 20, 16]
  shape_3A : ∀ c ∈ tab6Set a z b z₁ y 2, IsShapeD8TimesS3 ↥(Gx y ⊓ Gx c)
  shape_4B : ∀ c ∈ tab6Set a z b z₁ y 4, IsShapeTwoTwoTimesD8 ↥(Gx y ⊓ Gx c)
  shape_5A : ∀ c ∈ tab6Set a z b z₁ y 5, IsNonsplitDoubleCoverOfS5 ↥(Gx y ⊓ Gx c)
  shape_5E : ∀ c ∈ tab6Set a z b z₁ y 6, IsShapeZ2TimesD10 ↥(Gx y ⊓ Gx c)
  shape_6A : ∀ c ∈ tab6Set a z b z₁ y 7, IsShapeZ2TimesD8 ↥(Gx y ⊓ Gx c)

@[expose] def QuotShape (M N : Subgroup H) (P : Type*) [Group P] : Prop :=
  ∃ (_ : (N.subgroupOf M).Normal), Nonempty (↥M ⧸ N.subgroupOf M ≃* P)

@[expose] def tabXSet (a z b z₁ : H) : Fin 2 → Set H :=
  ![{c | IsConj b c ∧ c ∈ Gx z ∧ HIsA a z b (a * z * c)},
    {c | IsConj b c ∧ c ∈ Gx z ∧ HIsB z z₁ (a * z * c)}]

structure TableXData (a z b z₁ : H) : Prop where
  shape_K : IsShapeK ↥(commutator H ⊓ Gx z)
  partition : IsOrbitPartition (Gx z) {c | IsConj b c ∧ c ∈ Gx z} (tabXSet a z b z₁)
  card_stab : StabCard (Gx z) (tabXSet a z b z₁) ![768, 384]
  o1_mem : ∀ c ∈ tabXSet a z b z₁ 0, c ∈ CFSG.Open.pCoreOf 2 (Gx z)
  o1_card_R : ∀ c ∈ tabXSet a z b z₁ 0,
    Nat.card ↥(Gx z ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx z)) = 2 ^ 7
  o1_card_R_X' : ∀ c ∈ tabXSet a z b z₁ 0,
    Nat.card ↥(Gx z ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx z) ⊓ derivedOf (Gx z)) = 2 ^ 6
  o1_card_X' : ∀ c ∈ tabXSet a z b z₁ 0,
    Nat.card ↥(Gx z ⊓ Gx c ⊓ derivedOf (Gx z)) = 2 ^ 6 * 3
  o1_quot : ∀ c ∈ tabXSet a z b z₁ 0,
    QuotShape (Gx z ⊓ Gx c ⊓ derivedOf (Gx z))
      (Gx z ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx z) ⊓ derivedOf (Gx z)) (Z 3)
  o2_not_mem : ∀ c ∈ tabXSet a z b z₁ 1, c ∉ CFSG.Open.pCoreOf 2 (Gx z)
  o2_R : ∀ c ∈ tabXSet a z b z₁ 1,
    IsElemTwo 5 (Gx z ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx z))
  o2_R_X' : ∀ c ∈ tabXSet a z b z₁ 1,
    IsElemTwo 4 (Gx z ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx z) ⊓ derivedOf (Gx z))
  o2_card_X' : ∀ c ∈ tabXSet a z b z₁ 1,
    Nat.card ↥(Gx z ⊓ Gx c ⊓ derivedOf (Gx z)) = 2 ^ 5 * 3
  o2_quot : ∀ c ∈ tabXSet a z b z₁ 1,
    QuotShape (Gx z ⊓ Gx c ⊓ derivedOf (Gx z))
      (Gx z ⊓ Gx c ⊓ CFSG.Open.pCoreOf 2 (Gx z) ⊓ derivedOf (Gx z)) (Sym 3)
  quot_derived : QuotShape (Gx z) (derivedOf (Gx z)) (Elem2 2)
  relIndex_X'R :
    (derivedOf (Gx z) ⊔ CFSG.Open.pCoreOf 2 (Gx z)).relIndex (Gx z) = 2
  K_ne : commutator H ⊓ Gx z ≠ derivedOf (Gx z) ⊔ CFSG.Open.pCoreOf 2 (Gx z)
  pCore_derived : CFSG.Open.pCoreOf 2 (derivedOf (Gx z)) =
      derivedOf (Gx z) ⊓ CFSG.Open.pCoreOf 2 (Gx z) ∧
    CFSG.Open.pCoreOf 2 (commutator H ⊓ Gx z) = derivedOf (Gx z) ⊓ CFSG.Open.pCoreOf 2 (Gx z)
  center_derived : centerOf (derivedOf (Gx z)) =
      centerOf (CFSG.Open.pCoreOf 2 (derivedOf (Gx z))) ∧
    Nonempty (↥(centerOf (derivedOf (Gx z))) ≃* Z 2 × Z 4)
  three_centralizer : ∀ σ ∈ Gx z, orderOf σ = 3 → ∃ c ∈ tabXSet a z b z₁ 0,
    CFSG.Open.pCoreOf 2 (Gx z) ⊓ Gx σ =
        Subgroup.closure ((centerOf (derivedOf (Gx z)) : Set H) ∪ {c}) ∧
      (derivedOf (Gx z) ⊓ CFSG.Open.pCoreOf 2 (Gx z)) ⊓ Gx σ = centerOf (derivedOf (Gx z))

structure TwoFourData {H : Type} [Group H] (X : Subgroup H) : Prop where
  card_derived : Nat.card ↥(derivedOf X) = 960
  elem_two : IsElemTwo 4 (CFSG.Open.pCoreOf 2 (derivedOf X))
  irreducible : ∀ S : Subgroup H, S ≤ CFSG.Open.pCoreOf 2 (derivedOf X) →
    (∀ g ∈ X, ∀ s ∈ S, g * s * g⁻¹ ∈ S) → S = ⊥ ∨ S = CFSG.Open.pCoreOf 2 (derivedOf X)

end Vocabulary

structure SuborbitFacts : Prop where
  sylow_centre : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → ∀ T : Subgroup H, T ≤ Gx z → Nat.card T = 2 ^ 11 →
      centerOf T = Subgroup.zpowers a ⊔ Subgroup.zpowers z
  tableIV : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
      ∀ y : H, IsConj b y → TableIVData a z b z₁ y
  tableVI : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
      ∀ y : H, IsConj (a * z) y → TableVIData a z b z₁ y
  tableVI_5A_b : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
      ∀ y : H, IsConj (a * z) y → ∀ c ∈ tab6Set a z b z₁ y 5, ∃ s ∈ Gx y ⊓ Gx c, IsConj b s
  two_four : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → TwoFourData (Gx z₁)
  tableX : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b → ∀ x : H, IsConj z x → TableXData a x b z₁
  simple_2S5 : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ S : Subgroup H, IsSimpleGroup ↥S → ∀ t : ↥S, t ^ 2 = 1 → t ≠ 1 →
      IsNonsplitDoubleCoverOfS5 ↥(Subgroup.centralizer ({t} : Set ↥S)) → IsShapeU35 ↥S
  eleven_one_class : ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ x y : H, orderOf x = 11 → orderOf y = 11 → IsConj x y

structure M11Facts : Prop where
  perfect : ∀ (M : Type) [Group M], IsSporadic M .M11 → _root_.commutator M = ⊤
  center_trivial : ∀ (M : Type) [Group M], IsSporadic M .M11 → ∀ t : M, (∀ s : M, s * t = t * s) →
    t = 1
  one_class : ∀ (M : Type) [Group M], IsSporadic M .M11 → ∀ s t : M, s ^ 2 = 1 → t ^ 2 = 1 →
    s ≠ 1 → t ≠ 1 → IsConj s t
  centralizer_GL23 : ∀ (M : Type) [Group M], IsSporadic M .M11 → ∀ t : M, t ^ 2 = 1 → t ≠ 1 →
    Nonempty (↥(Subgroup.centralizer ({t} : Set M)) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
  inv_not_two_group : ¬ IsPGroup 2 ↥(Subgroup.closure
    {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) | g ^ 2 = 1})
  exists_order_five : ∀ (M : Type) [Group M], IsSporadic M .M11 → ∀ s : M, s ^ 2 = 1 → s ≠ 1 →
    ∃ t : M, t ^ 2 = 1 ∧ orderOf (s * t) = 5

structure U35Facts : Prop where
  card_eq : ∀ (X : Type) [Group X], IsShapeU35 X → Nat.card X = 126000
  one_class : ∀ (X : Type) [Group X], IsShapeU35 X → ∀ s t : X, s ^ 2 = 1 → t ^ 2 = 1 →
    s ≠ 1 → t ≠ 1 → IsConj s t

end CFSG.EvenSporadicStandard.HNRecog.Section3
