module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactCTy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ w : G, w ∈ normalizer (L : Set G) → w * w ∈ centralizer (L : Set G) →
      (w ∉ L ⊔ centralizer (L : Set G) ↔
        (InducesTypeSome L w 5 1 2 1 ∨ InducesTypeSome L w 5 1 4 (-1)))

@[expose] def Asc82FactCSw : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ (z : G) (K1 K2 : Subgroup G), IsI4PlusIn L z → Sl23PocketIn L z K1 → Sl23PocketIn L z K2 →
      K1 ≠ K2 → ∀ r : G, r * z = z * r → InducesTypeSome L r 5 1 4 (-1) →
        CFSG.conjugate K1 r = K2

@[expose] def Asc82FactCLay : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ w : G, InducesTypeSome L w 5 1 4 (-1) →
      CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({w} : Set G)) ≠ ⊥

@[expose] def Asc82FactCI2p : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ s w : G, InducesTypeSome L s 5 1 2 1 → InducesTypeSome L w 5 1 2 1 →
      ∃ l ∈ L, (l⁻¹ * s * l)⁻¹ * w ∈ centralizer (L : Set G)

@[expose] def Asc82FactCI2m : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsPSp43 L →
    ∀ u v : G, u ∈ L → v ∈ L → InducesTypeSome L u 5 1 2 (-1) → InducesTypeSome L v 5 1 2 (-1) →
      ∃ l ∈ L, l⁻¹ * u * l = v

@[expose] def Asc82FactCY : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → IsPSp43 L → S ≤ normalizer (L : Set G) →
    centralizer (L : Set G) ⊓ S = zpowers t → IsSylow2Of (S ⊓ L) L →
    ∀ r ∈ S, orderOf r = 2 → InducesTypeSome L r 5 1 4 (-1) →
      secA2 t r K1 K2 ≠ secA t S L →
      (∀ X : Subgroup G, IsNormalE32In S X ↔ (X = secA t S L ∨ X = secA2 t r K1 K2)) →
      ∀ s ∈ normalizer (S : Set G), s * s = 1 → s * z = z * s → s⁻¹ * t * s = t * z →
        (∀ a ∈ secA t S L, s⁻¹ * a * s ∈ secA2 t r K1 K2) →
        ∃ x ∈ S, (x⁻¹ * s * x * s) * (x⁻¹ * s * x * s) = 1 ∧ x⁻¹ * s * x * s ∉ zpowers z

structure Asc82FactsC : Prop where
  ty : Asc82FactCTy
  sw : Asc82FactCSw
  lay : Asc82FactCLay
  i2p : Asc82FactCI2p
  i2m : Asc82FactCI2m
  y : Asc82FactCY

end CFSG.OddStandard.SmallF3.Omega
