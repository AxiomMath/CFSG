module

public import CFSG.GH74.QTGen4.Recog.Ku.KuCloseDef
public import CFSG.Quasithin.Recognition.L34AmalgamParabolic
public import CFSG.GH74.QTGen4.Recog.Ku.Hyp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam
open scoped IsMulCommutative

class KuLeaf (L : Prop) : Prop where
  holds : L

@[expose] def LeafCardKuA : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z → Nat.card (kuA P H) = 16

@[expose] def LeafIsMulCommutativeKuA : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z → IsMulCommutative (kuA P H)

@[expose] def LeafHInfCentralizerKuA : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z → H ⊓ Subgroup.centralizer (kuA P H : Set G) = kuA P H

@[expose] def LeafEqKuAOfElemAbelian : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z → ∀ {E' : Subgroup G},
      E' ≤ pCoreOf 2 H → IsElemAbelian 2 E' → Nat.card E' = 16 → E' = kuA P H

@[expose] def LeafTInfCentralizerKuWLeKuA : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z → T ⊓ Subgroup.centralizer (kuW P H : Set G) ≤ kuA P H

@[expose] def LeafKuV2LeKuW : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z → kuV2 T M ≤ kuW P H

@[expose] def LeafExistsA6Model : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z →
      Nonempty (KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)

@[expose] def LeafExistsIsParabolicL1 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z → ∃ a b : G, IsParabolic (oTwoUpper M) (pCoreOf 2 M) a b

@[expose] def LeafOTwoUpperInfL2 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z →
    ∀ (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z),
      oTwoUpper M ⊓ Ψ.L2 = oTwoUpper M ⊓ kuN P H

@[expose] def LeafCardOTwoUpperInfL2 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z →
    ∀ (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z),
      Nat.card ↥(oTwoUpper M ⊓ Ψ.L2) = 192

@[expose] def LeafKuNEqL2DoubleCoset : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z →
    ∀ (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {t : G},
      t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G) → t ∉ oTwoUpper M →
      ∀ g ∈ kuN P H, g ∈ Ψ.L2 ∨ ∃ a ∈ Ψ.L2, ∃ b ∈ Ψ.L2, g = a * t * b

@[expose] def LeafExistsY2TJ : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G},
    KuHyp G T M H P z →
    ∀ (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z),
      ∃ y₂ t j t₁ : G, y₂ ∈ oTwoUpper M ⊓ Ψ.L2 ∧ orderOf y₂ = 3 ∧
        t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G) ∧ t ∉ oTwoUpper M ∧ t * t = 1 ∧
        t * y₂ * t⁻¹ = y₂⁻¹ ∧
        j ∈ Ψ.L2 ∧ j ∉ oTwoUpper M ∧ j * j = 1 ∧ j * y₂ * j⁻¹ = y₂⁻¹ ∧
        (t * j) ^ 3 = 1 ∧
        t₁ ∈ oTwoUpper M ∧ t₁ ∉ kuN P H ∧ t₁ * t₁ = 1 ∧ t₁ * y₂ * t₁⁻¹ = y₂⁻¹

@[expose] def LeafKuCloseHolds : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G}
   ,
    KuHyp G T M H P z →
    ∀ (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z),
      KuClose' T M H P z Ψ

end CFSG.GH74.QTGen4.Ku
