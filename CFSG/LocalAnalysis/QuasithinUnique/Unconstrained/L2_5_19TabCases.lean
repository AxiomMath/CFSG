module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabJ2Cent
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL34
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL5
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Main
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSMain
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs3

public section

namespace CFSG.QuasithinUnique.Id2519.Tab

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

@[expose] def TabAutCentSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    PatSp4 X K →
    ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) → Y ≤ Subgroup.centralizer (K : Set G) →
      (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2

theorem tabAutCentA
    :
    ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
      t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
      K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) →
      PatA X K t →
      ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) → Y ≤ Subgroup.centralizer (K : Set G) →
        (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2 := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat Y hYn hYc
  exact L34.tabAutCent_patA G X K t hXq ht ht2 hcomm hK hpat Y hYn hYc

theorem tabAutCentB
    :
    ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
      t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
      K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) →
      PatB X K t →
      ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) → Y ≤ Subgroup.centralizer (K : Set G) →
        (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2 := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat Y hYn hYc
  exact tabAutCent_patB G X K t hXq ht ht2 hcomm hK hpat Y hYn hYc

theorem tabAutCentA8 :
    ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
      t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
      K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) →
      PatA8 X K t →
      ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) → Y ≤ Subgroup.centralizer (K : Set G) →
        (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2 := by
  intro G _ _ X K t _ _ _ _ hK hpat Y hYn hYc
  exact A8.tabAutCent_patA8 G X K t hK hpat Y hYn hYc

theorem tabAutCentL5 :
    ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
      t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
      K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) →
      PatL5 X K →
      ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (X : Set G) → Y ≤ Subgroup.centralizer (K : Set G) →
        (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y ≤ 2 := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat Y hYn hYc
  exact L5.tabAutCent_patL5 G X K t hXq ht ht2 hcomm hK hpat Y hYn hYc

theorem tabAutCentSp4 : TabAutCentSp4 := USp4.tabAutCentSp4

theorem tabAutCent
    : TabAutCent := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat Y hYn hYc
  rcases hpat with h | h | h | h | h
  · exact tabAutCentA G X K t hXq ht ht2 hcomm hK h Y hYn hYc
  · exact tabAutCentB G X K t hXq ht ht2 hcomm hK h Y hYn hYc
  · exact tabAutCentSp4 G X K t hXq ht ht2 hcomm hK h Y hYn hYc
  · exact tabAutCentL5 G X K t hXq ht ht2 hcomm hK h Y hYn hYc
  · exact tabAutCentA8 G X K t hXq ht ht2 hcomm hK h Y hYn hYc

theorem tabConjB :
    ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
      t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
      K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) →
      PatB X K t → Subgroup.center ↥X = ⊥ →
      ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u := by
  intro G _ _ X K t hXq ht ht2 _ hK hpat hZ
  exact tabConj_patB G X K t hXq ht ht2 hK hpat hZ

theorem tabConjA1
    :
    ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
      t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
      K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) →
      PatA X K t → Subgroup.center ↥X = ⊥ →
      ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat hZ
  exact L34.tabConj_patA G X K t hXq ht ht2 hcomm hK hpat hZ

theorem tabConjL5 :
    ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
      t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
      K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
        (X ⊓ Subgroup.centralizer ({t} : Set G)) →
      PatL5 X K →
      ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat
  exact L5.tabConj_patL5 G X K t hXq ht ht2 hcomm hK hpat

@[expose] def TabConjRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    ((PatA X K t ∧ Nat.card (Subgroup.center ↥X) = 2) ∨
      (PatHS X K t ∧ Subgroup.center ↥X = ⊥)) →
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u

@[expose] def TabConjA2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    PatA X K t → Nat.card (Subgroup.center ↥X) = 2 →
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u

@[expose] def TabConjSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    PatSp4 X K →
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u

@[expose] def TabConjHS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), CFSG.IsQuasisimple ↥X →
    t ∈ Subgroup.normalizer (X : Set G) → t * t = 1 → ⁅X, Subgroup.zpowers t⁆ = X →
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) →
    PatHS X K t → Subgroup.center ↥X = ⊥ →
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u

theorem tabConjSp4 : TabConjSp4 := USp4.tabConjSp4

theorem tabConjHS
    : TabConjHS := UHS.tabConjHS

theorem tabConjRest_of_clauses (hA2 : TabConjA2) (hHS : TabConjHS) : TabConjRest := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat u huK hu2
  rcases hpat with ⟨hA, hZ⟩ | ⟨hH, hZ⟩
  · exact hA2 G X K t hXq ht ht2 hcomm hK hA hZ u huK hu2
  · exact hHS G X K t hXq ht ht2 hcomm hK hH hZ u huK hu2

theorem tabConj_of_rest
    (hrest : TabConjRest) : TabConj := by
  intro G _ _ X K t hXq ht ht2 hcomm hK hpat u huK hu2
  rcases hpat with ⟨hA, hZA⟩ | ⟨hB, hZB⟩ | hSp | hL5 | hHS
  · by_cases hZ : Subgroup.center ↥X = ⊥
    · exact tabConjA1 G X K t hXq ht ht2 hcomm hK hA hZ u huK hu2
    · have hpos : 0 < Nat.card (Subgroup.center ↥X) := Nat.card_pos
      have h1 : Nat.card (Subgroup.center ↥X) ≠ 1 := fun h => hZ (Subgroup.card_eq_one.mp h)
      exact hrest G X K t hXq ht ht2 hcomm hK (Or.inl ⟨hA, by omega⟩) u huK hu2
  · exact tabConjB G X K t hXq ht ht2 hcomm hK hB hZB u huK hu2
  · exact tabConjSp4 G X K t hXq ht ht2 hcomm hK hSp u huK hu2
  · exact tabConjL5 G X K t hXq ht ht2 hcomm hK hL5 u huK hu2
  · exact hrest G X K t hXq ht ht2 hcomm hK (Or.inr hHS) u huK hu2

theorem tabJ2Cover
    : TabJ2Cover := by
  intro G _ _ X K t hXq ht ht2 _ _ hpat hcard i hi hi1
  refine tabJ2Cover_of_isPGroup G X K t hXq ht ht2 hpat ?_ i hi hi1
  have hpos : 0 < Nat.card (Subgroup.center ↥X) := Nat.card_pos
  have : Nat.card (Subgroup.center ↥X) = 1 ∨ Nat.card (Subgroup.center ↥X) = 2 := by omega
  rcases this with h | h
  · exact IsPGroup.of_card (n := 0) (by simp [h])
  · exact IsPGroup.of_card (n := 1) (by simp [h])

theorem tabConj_of_clauses
    (hA2 : TabConjA2) (hHS : TabConjHS) : TabConj :=
  tabConj_of_rest (tabConjRest_of_clauses hA2 hHS)

theorem tabConj_of_A2
    (hA2 : TabConjA2) : TabConj := tabConj_of_clauses hA2 tabConjHS

end CFSG.QuasithinUnique.Id2519.Tab
