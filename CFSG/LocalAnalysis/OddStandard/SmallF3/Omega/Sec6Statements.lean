module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.GH74.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma61 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Plus L → ∀ x : G, orderOf x = 2 → x ∈ centralizer ({t} : Set G) →
      IsOmega5 (layerCent L x) →
        ∃ I : Subgroup G, IsComponentIn I (centralizer ({x} : Set G)) ∧ layerCent L x ≤ I ∧
          (IsOmega5 I ∨ IsOmega6Plus I)

@[expose] def Asc82Lemma63 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    Asc82Hyp62 G → ∀ x : G, orderOf x = 2 →
      ∀ X₁ X₂ : Subgroup G, IsComponentIn X₁ (centralizer ({x} : Set G)) → InFStar X₁ →
        IsComponentIn X₂ (centralizer ({x} : Set G)) → InFStar X₂ → X₁ = X₂

@[expose] def Asc82Lemma64 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    Asc82Hyp62 G → ∀ X : Subgroup G, InC X → InFStar X →
      ∀ T : Subgroup G, IsSylow2Of T (centralizer (X : Set G)) →
        IsCyclic T ∨ ((IsL3Eps3 X ∨ IsL29 X ∨ IsOmega5 X) ∧ CFSG.Open.pRank 2 T = 2) ∨
          ((IsU33 X ∨ IsL29 X) ∧ CFSG.GH74.sectionalTwoRank T ≤ 3)

@[expose] def Asc82Lemma65 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    Asc82Hyp62 G → ∀ X : Subgroup G, InC X → InFStar X →
      CFSG.Open.pRank 2 (normalizer (X : Set G)) ≤ 6

@[expose] def Asc82Lemma66 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Minus L → ∀ z : G, orderOf z = 2 → z ∈ L → IsConj t (t * z)

@[expose] def Asc82Lemma67a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Minus L → Asc82Hyp62 G →
      ∀ E : Subgroup G, IsElemAb2 E 8 → ∀ x : G, orderOf x = 2 →
        6 ≤ CFSG.Open.pRank 2 (E ⊓ centralizer ({x} : Set G)) →
          ∀ K : Subgroup G, IsComponentIn K (centralizer ({x} : Set G)) → ¬ InFStar K

@[expose] def Asc82Lemma67b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Minus L → Asc82Hyp62 G →
      ∀ E : Subgroup G, IsElemAb2 E 8 → ∀ z : G, orderOf z = 2 → z ∈ L →
        (∀ y : G, orderOf y = 2 → (∃ α, InducesTypeSome L y 6 (-1) 3 α) → IsConj t y) →
        (∀ y : G, orderOf y = 2 → y ∈ normalizer (L : Set G) → (∀ l ∈ L, l⁻¹ * z * l ≠ y) →
          CFSG.Open.pRank 2 (E ⊓ centralizer ({y} : Set G)) < 6) ∧
        (∀ s : G, IsConj t s → ∀ y ∈ E ⊓ centralizer ({s} : Set G), y ≠ 1 → IsConj z y)

@[expose] def Asc82Lemma68 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Minus L → ∀ B : Subgroup G, IsElemAb2 B 4 → B ≤ L →
      ∀ g : G, g⁻¹ * t * g ≠ t → g⁻¹ * t * g ∈ cosetSet t B → B ≤ CFSG.conjugate L g →
        IsSylow2Of (zpowers t) (centralizer (L : Set G)) ∧
          ConjTwoTransOn (normalizer ((zpowers t ⊔ B : Subgroup G) : Set G)) (cosetSet t B)

end CFSG.OddStandard.SmallF3.Omega
