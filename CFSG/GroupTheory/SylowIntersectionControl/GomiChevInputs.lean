module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools Subgroup

@[expose] def GomiChevIsolated : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L I : Subgroup G), IsGomiChevTwo ↥L → IsPGroup 2 I →
    I ≤ normalizer (L : Set G) → IsPIsolatedOver 2 (L ⊓ centralizer (I : Set G)) ⊥ →
    (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨ IsGomiSz (↥L ⧸ center ↥L)) ∨
      ((IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L)) ∧
        ∀ U : Subgroup G, IsSylowOf 2 U L → I ≤ normalizer (U : Set G) →
          ∃ a ∈ I, ∃ P : Subgroup G, L ⊓ normalizer (U : Set G) < P ∧ P < L ∧
            a ∉ normalizer (P : Set G))

@[expose] def GomiChevParabolic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L I : Subgroup G), IsGomiChevTwo ↥L → I ≤ L → IsPGroup 2 I →
    pCoreOf 2 (L ⊓ normalizer (I : Set G)) = I →
    ∃ U : Subgroup G, IsSylowOf 2 U L ∧ L ⊓ normalizer (U : Set G) ≤ L ⊓ normalizer (I : Set G)

@[expose] def GomiChevTrichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L X H : Subgroup G), L.Normal → IsGomiChevTwo ↥L →
    L ≤ X → H ≠ ⊥ → IsPGroup 2 H → H ≤ X →
    IsPIsolatedOver 2 (normalizer (H : Set G) ⊓ X) H →
    IsPIsolatedOver 2 (L ⊓ centralizer (H : Set G)) ⊥ ∨
    (∃ I : Subgroup G, I ≠ ⊥ ∧ I ≤ L ∧ IsPGroup 2 I ∧
      pCoreOf 2 (L ⊓ normalizer (I : Set G)) = I ∧
      (∃ K : Subgroup G, H ≤ K ∧ K ≤ normalizer (H : Set G) ⊓ X ∧
        (K.subgroupOf (normalizer (H : Set G) ⊓ X)).IsSubnormal ∧ 2 ∣ H.relIndex K ∧
        K ≤ normalizer (I : Set G)) ∧
      Odd (normalizer (I : Set G)).index) ∨
    ((IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L)) ∧
      (∃ U : Subgroup G, IsSylowOf 2 U L ∧
        L ⊓ normalizer (U : Set G) < L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) ∧
      L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) < L ∧
      pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L ∧
      ∃ g : G, IsPGroup 2 (zpowers g) ∧ ∃ U : Subgroup G, IsSylowOf 2 U L ∧
        g ∈ normalizer (U : Set G) ∧ ∃ P : Subgroup G, L ⊓ normalizer (U : Set G) < P ∧ P < L ∧
          g ∉ normalizer (P : Set G))

@[expose] def GomiChevCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L X H : Subgroup G), L.Normal → IsGomiChevTwo ↥L →
    ¬ (IsGomiL2 (↥L ⧸ center ↥L) ∨ IsGomiU3 (↥L ⧸ center ↥L) ∨ IsGomiSz (↥L ⧸ center ↥L)) →
    ((IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L)) →
      ∃ T : Sylow 2 G, ¬ IsGomiParabolicSwap (T : Subgroup G) L) →
    L ≤ X → H ≠ ⊥ → IsPGroup 2 H → H ≤ X →
    IsPIsolatedOver 2 (normalizer (H : Set G) ⊓ X) H →
    ∃ Y : Subgroup G, Y ≠ ⊤ ∧ Odd Y.index ∧
      (∃ K : Subgroup G, H ≤ K ∧ K ≤ normalizer (H : Set G) ⊓ X ∧
        (K.subgroupOf (normalizer (H : Set G) ⊓ X)).IsSubnormal ∧ 2 ∣ H.relIndex K ∧ K ≤ Y) ∧
      L ⊓ normalizer ((Y ⊓ L : Subgroup G) : Set G) = Y ⊓ L ∧
      twoResidual ((Y ⊓ L) ⊓ centralizer (pCoreOf 2 (Y ⊓ L) : Set G)) ≤
        L ⊓ centralizer (L : Set G)

end CFSG.GroupTheory
