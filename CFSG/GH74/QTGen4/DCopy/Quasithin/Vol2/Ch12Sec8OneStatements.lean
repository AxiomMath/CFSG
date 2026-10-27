module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch12Sec8OneStatements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Lemma12_8_3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Hyp1281One G T L V n →
    (autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V = ⊤ ∧
      autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V =
        autOn L V) ∧
    (∀ (i : ℕ) (W₁ W₂ : Subgroup G), W₁ ≤ V → W₂ ≤ V → Nat.card W₁ = 2 ^ i →
      Nat.card W₂ = 2 ^ i → ∃ l ∈ L, CFSG.conjugate W₁ l = W₂) ∧
    (∀ (i : ℕ) (Vi : Subgroup G), IsTSub T V Vi i → ∀ g : G, Vi ≤ CFSG.conjugate V g →
      ∃ k ∈ Subgroup.normalizer (Vi : Set G), CFSG.conjugate V k = CFSG.conjugate V g) ∧
    ∀ V₁ : Subgroup G, IsTSub T V V₁ 1 →
      ¬ Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Lemma12_8_4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ), Hyp1281One G T L V n →
    ∀ V₁ H : Subgroup G, IsTSub T V V₁ 1 → IsHzOne T L V₁ H →
      AlmostSpecialHyp V V₁ L T H ∧
      (tildeOf V₁ (conjClosure V H) ≤ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) ∧
        IsTwoReducedIn (tildeOf V₁ H) (tildeOf V₁ (conjClosure V H))) ∧
      frattiniOf (conjClosure V H) ≤ V₁ ∧
      centralizerMod V₁ H (conjClosure V H) = pCoreOf 2 H

@[expose] def Lemma12_8_10_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      zU128 V V₁ ⊓ CFSG.conjugate (u128 V V₁) g =
          (zU128 V V₁ ⊓ CFSG.conjugate (zU128 V V₁) g) ⊔ V₁ ∧
      zU128 V V₁ ⊓ CFSG.conjugate (zU128 V V₁) g = centerOf (i128 T L V V₁) ∧
      (V₁ < zU128 V V₁ ⊓ CFSG.conjugate (u128 V V₁) g →
        quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) ≠ ⊥) ∧
      (⁅w128 V V₁ V₂, CFSG.conjugate (zU128 V V₁) g⁆ ≤ zU128 V V₁ ⊔ V₂ ∧
        ∀ x ∈ CFSG.conjugate (zU128 V V₁) g,
          (zU128 V V₁).relIndex (⁅u128 V V₁, Subgroup.zpowers x⁆ ⊔ zU128 V V₁) ≤ 4) ∧
      (CFSG.conjugate (zU128 V V₁) g ≤ u128 V V₁ →
        zU128 V V₁ = centerOf (i128 T L V V₁) ⊔ V₁ ∧ centerOf (i128 T L V V₁) ⊓ V₁ = ⊥ ∧
          ⁅L, centerOf (i128 T L V V₁)⁆ = ⊥) ∧
      (CFSG.conjugate (zU128 V V₁) g ⊓
          centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) =
          CFSG.conjugate (zU128 V V₁) g ⊓
            centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) ∧
        CFSG.conjugate (zU128 V V₁) g ⊓
            centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) =
          CFSG.conjugate (zU128 V V₁) g ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ∧
        CFSG.conjugate (zU128 V V₁) g ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) =
          CFSG.conjugate (zU128 V V₁) g ⊓ u128 V V₁ ∧
        CFSG.conjugate (zU128 V V₁) g ⊓ u128 V V₁ =
          (CFSG.conjugate (zU128 V V₁) g ⊓ zU128 V V₁) ⊔ CFSG.conjugate V₁ g ∧
        (CFSG.conjugate (zU128 V V₁) g ⊓ zU128 V V₁) ⊔ CFSG.conjugate V₁ g =
          centerOf (i128 T L V V₁) ⊔ CFSG.conjugate V₁ g ∧
        centerOf (i128 T L V V₁) ⊔ CFSG.conjugate V₁ g ≤ u128 V V₁)

@[expose] def Lemma12_8_11_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      ⁅w128 V V₁ V₂, CFSG.conjugate (w128 V V₁ V₂) g⁆ ≤
          w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g ∧
      IsElemAbelian 2 (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g) ∧
      centralizerMod (zU128 V V₁) (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g)
          (CFSG.conjugate (w128 V V₁ V₂) g) ⊔ zU128 V V₁ = V₂ ⊔ zU128 V V₁

@[expose] def Lemma12_8_12_two_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V₂ : Set G) ≤
          Subgroup.normalizer ((CFSG.conjugate (w128 V V₁ V₂) g ⊔
            centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) :
              Subgroup G) : Set G) ∧
      Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.normalizer (V₂ : Set G) ≤
          Subgroup.normalizer ((CFSG.conjugate (zU128 V V₁) g ⊔
            centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) :
              Subgroup G) : Set G)

@[expose] def Lemma12_8_13_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
      V ≤ w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g ∧
      CFSG.conjugate (zU128 V V₁) g ≤ Subgroup.centralizer (V : Set G) ∧
      (V₁ < zU128 V V₁ → ¬ CFSG.conjugate (zU128 V V₁) g ≤
        centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁)) ∧
      CFSG.Open.pRank 3 (centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂) ≤ 1

end CFSG.Quasithin.H13
