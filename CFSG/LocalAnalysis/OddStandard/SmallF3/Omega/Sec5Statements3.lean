module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma513 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ x ∈ centralizer ({z} : Set G),
        x⁻¹ * t * x ∈ DeltaT5 z (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) →
          twoRes (CFSG.conjugate L x ⊓ centralizer ({z} : Set G)) = K₁ ⊔ K₂ ∧
            CFSG.conjugate (K₁ ⊔ K₂) x = K₁ ⊔ K₂

@[expose] def Asc82Lemma514 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ⁅K₁ ⊔ K₂, CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h⁆ = ⊥ ∧
        (∀ i j : Fin 4, i ≠ j → ⁅Kfam5 K₁ K₂ h i, Kfam5 K₁ K₂ h j⁆ = ⊥) ∧
        ∀ i : Fin 4,
          Nonempty (↥(Kfam5 K₁ K₂ h i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))

@[expose] def Asc82Lemma515a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ d ∈ Delta5 z (Gamma5 K₁ K₂ h), IsTwoU43 ↥(layerC5 d)

@[expose] def Asc82Lemma515b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ d ∈ Delta5 z (Gamma5 K₁ K₂ h),
        (∃ P : Subgroup G, IsKOf (Gamma5 K₁ K₂ h) d P) ∧
          ∀ P : Subgroup G, IsKOf (Gamma5 K₁ K₂ h) d P →
            P = twoRes (centralizer ({z} : Set G) ⊓ layerC5 d)

@[expose] def Asc82Lemma515c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ d ∈ Delta5 z (Gamma5 K₁ K₂ h),
        ∃ (S' : Subgroup G) (r' : G) (B' A' P₁ P₂ : Subgroup G) (h' : G),
          Sec5HCtx G d (layerC5 d) S' z r' B' A' P₁ P₂ h' ∧
            Gamma5 P₁ P₂ h' = Gamma5 K₁ K₂ h

@[expose] def Asc82Lemma516a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      Qsub K₁ K₂ h ⊔ oddCoreIn (centralizer ({t} : Set G)) =
        centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)

@[expose] def Asc82Lemma517 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      (∀ n ∈ normalizer (Qsub K₁ K₂ h : Set G), ∀ P ∈ Gamma5 K₁ K₂ h,
          CFSG.conjugate P n ∈ Gamma5 K₁ K₂ h) ∧
        ∀ P ∈ Gamma5 K₁ K₂ h, ∀ P' ∈ Gamma5 K₁ K₂ h,
          ∃ n ∈ normalizer (Qsub K₁ K₂ h : Set G), CFSG.conjugate P n = P'

@[expose] def Asc82Lemma518b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ (n : ℕ) (U : Subgroup G), U ≤ normalizer (Qsub K₁ K₂ h : Set G) →
        IsElemAbelianModSub
            (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)) U →
          (centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G)) (Qsub K₁ K₂ h)).relIndex U =
              2 ^ n → n ≤ 3

@[expose] def Asc82Lemma519 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∀ q ∈ Qsub K₁ K₂ h, ∀ x ∈ centralizer ({z} : Set G),
        x⁻¹ * q * x ∈ normalizer (Qsub K₁ K₂ h : Set G) → x⁻¹ * q * x ∈ Qsub K₁ K₂ h

@[expose] def Asc82Lemma520 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h → Chev3 G

end CFSG.OddStandard.SmallF3.Omega
