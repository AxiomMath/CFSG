module

public import CFSG.GH74.Uniqueness.SU.SU4Defs
public import CFSG.GH74.GLS.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.Uniqueness.SU.SU8

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.Blueprint

variable {G : Type} [Group G]

abbrev Hbar (H : Subgroup G) : Type _ := ↥H ⧸ pPrimeCore 2 ↥H

@[expose] def hbarImage (H X : Subgroup G) : Subgroup (Hbar H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H))

@[expose] def centralizerBar (H L : Subgroup G) : Subgroup G :=
  ((centralizer ((hbarImage H L : Subgroup (Hbar H)) : Set (Hbar H))).comap
    (QuotientGroup.mk' (pPrimeCore 2 ↥H))).map H.subtype

@[expose] def omegaOne (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {g : G | g ∈ X ∧ g * g = 1}

section Finite

variable [Finite G]

structure Hyp20A (z : G) (S L A : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kgh : KGH G
  z_invol : orderOf z = 2
  S_sylow_H : IsSylowIn (centralizer ({z} : Set G)) S
  L_comp : GLS.IsPCompIn 2 (centralizer ({z} : Set G)) L
  L_normal : centralizer ({z} : Set G) ≤ normalizer (L : Set G)
  L_bender : CFSG.BenderSuzuki.IsBenderGroup ↥(hbarImage (centralizer ({z} : Set G)) L) ∨
    Nonempty ((↥(hbarImage (centralizer ({z} : Set G)) L) ⧸
      center ↥(hbarImage (centralizer ({z} : Set G)) L)) ≃* CFSG.Theory.Comparator.SzModel 1)
  A_ge : omegaOne (S ⊓ L) ⊔ zpowers z ≤ A
  A_le : A ≤ L ⊔ centralizerBar (centralizer ({z} : Set G)) L
  A_elem : Open.IsElemAbelian 2 A
  A_strongly_closed : ∃ S' : Sylow 2 G, A ≤ (S' : Subgroup G) ∧
    ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S' : Subgroup G) → g⁻¹ * a * g ∈ A
  Q_tame : ∀ x : G, x ∉ normalizer (L : Set G) →
    (S ⊓ centralizerBar (centralizer ({z} : Set G)) L) ⊓
      conjSub x (S ⊓ centralizerBar (centralizer ({z} : Set G)) L) = ⊥
  S_sylow : IsSylowIn ⊤ S
  irreducible : ∀ B : Subgroup G, B ≤ A → B ≠ ⊥ → normalizer (A : Set G) ≤ normalizer (B : Set G) →
    B = A

@[expose] def Lemma202Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S L A : Subgroup G), Hyp20A z S L A →
    center ↥(hbarImage (centralizer ({z} : Set G)) L) = ⊥

@[expose] def Lemma203Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S L A : Subgroup G), Hyp20A z S L A →
    Nat.card A = 8 ∧
      ∃ _ : ((centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))).Normal,
        Nat.card (↥(normalizer (A : Set G)) ⧸
          (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))) = 21 ∧
        ∃ a b : ↥(normalizer (A : Set G)) ⧸
          (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G)), a * b ≠ b * a

@[expose] def IsL24 (X : Type) [Group X] : Prop := LieModel X .PSL 2 2 2

@[expose] def Lemma204Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S L A : Subgroup G), Hyp20A z S L A →
    IsL24 ↥(hbarImage (centralizer ({z} : Set G)) L)

@[expose] def Lemma205Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S L A : Subgroup G), Hyp20A z S L A →
    ∃ (Y : Type) (_ : Group Y), IsL24 Y ∧
      Nonempty (Hbar (centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Y)

@[expose] def Prop201Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S L A : Subgroup G), Hyp20A z S L A →
    (∃ (Y : Type) (_ : Group Y), IsL24 Y ∧
      Nonempty (Hbar (centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Y)) ∧
    (∃ _ : ((centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))).Normal,
      Nat.card (↥(normalizer (A : Set G)) ⧸
        (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))) = 21 ∧
      ∃ a b : ↥(normalizer (A : Set G)) ⧸
        (centralizer (A : Set G)).subgroupOf (normalizer (A : Set G)), a * b ≠ b * a) ∧
    (pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ →
      ∃ (Y : Type) (_ : Group Y), IsL24 Y ∧
        Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Y))

end Finite

end CFSG.GH74.Uniqueness.SU.SU8
