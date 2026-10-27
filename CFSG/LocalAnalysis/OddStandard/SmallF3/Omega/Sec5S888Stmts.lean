module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactPocketsTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G) (z : G) (K₁ K₂ P : Subgroup G),
    orderOf z = 2 → Sl23PocketIn X z K₁ → Sl23PocketIn X z K₂ → K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ →
      K₁ ⊔ K₂ = twoRes (X ⊓ centralizer ({z} : Set G)) →
      Nonempty (↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) →
      Nonempty (↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) →
        Sl23PocketIn X z P → P ≤ K₁ ⊔ K₂ → P = K₁ ∨ P = K₂

@[expose] def Asc82FactRhoStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G) (z : G) (K₁ K₂ : Subgroup G),
    orderOf z = 2 → IsOm6Z2 L → oddCoreIn L = ⊥ → centerIn L = zpowers t →
      Sl23PocketIn L z K₁ → Sl23PocketIn L z K₂ → K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ →
        K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G)) →
        ∀ q ∈ K₁, orderOf q = 4 → ∀ c ∈ normalizer (L : Set G),
          K₁ ⊔ K₂ ≤ centralizer ({c} : Set G) →
          (∀ y ∈ L, (c * c) * y * (c * c)⁻¹ = z * y * z⁻¹) →
            LieModel ↥(layerCent L (q * c)) .PSU 3 3 1 ∧ K₂ ≤ layerCent L (q * c)

@[expose] def Asc82Lemma515Setting : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ d ∈ Delta5 z (Gamma5 K₁ K₂ h), ∃ I : Subgroup G, Sec5Setting G d I ∧
        ∃ P : Subgroup G, IsKOf (Gamma5 K₁ K₂ h) d P ∧ P ≤ I

@[expose] def Asc82Lemma518Parity : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ w ∈ normalizer (Qsub K₁ K₂ h : Set G),
        (∀ i, CFSG.conjugate (Kfam5 K₁ K₂ h i) w = Kfam5 K₁ K₂ h i) →
        w * w ∈ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h) →
          Even (Nat.card {i : Fin 4 // ∃ q ∈ twoCoreIn (Kfam5 K₁ K₂ h i),
            w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z})

@[expose] def Asc82FactOm6NRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G) (K₁ K₂ : Subgroup G),
    IsOm6Z2 L → oddCoreIn L = ⊥ → orderOf z = 2 → Sl23PocketIn L z K₁ → Sl23PocketIn L z K₂ →
      K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ → K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G)) →
        ∀ (n : ℕ) (E : Subgroup G),
          E ≤ normalizer (L : Set G) ⊓ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) →
          IsElemAbelianModSub (twoCoreIn (K₁ ⊔ K₂) ⊔
            (normalizer (L : Set G) ⊓ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))) E →
          (twoCoreIn (K₁ ⊔ K₂) ⊔
            (normalizer (L : Set G) ⊓ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G))).relIndex E
              = 2 ^ n → n ≤ 2

@[expose] def Asc82SylowContain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ T : Subgroup G, Qsub K₁ K₂ h ≤ T → IsSylow2Of T (normalizer (Qsub K₁ K₂ h : Set G)) →
        IsSylow2Of T (centralizer ({z} : Set G))

@[expose] def Asc82CHdLeN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ d ∈ Delta5 z (Gamma5 K₁ K₂ h),
        centralizer ({d} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (Qsub K₁ K₂ h : Set G)

end CFSG.OddStandard.SmallF3.Omega
