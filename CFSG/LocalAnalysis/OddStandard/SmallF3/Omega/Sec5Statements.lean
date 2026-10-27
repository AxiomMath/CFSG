module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec5Setting G t L → InCStar L

@[expose] def Asc82Lemma52a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec5Setting G t L →
    ∀ P : Sylow 2 (centralizer (L : Set G)), IsCyclic (P : Subgroup (centralizer (L : Set G)))

@[expose] def Asc82Lemma52b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec5Setting G t L →
    t ∈ L ∧ twoCoreIn L = zpowers t

@[expose] def Asc82Lemma53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec5Ctx G t L S z →
    omega1 (centerIn S) = zpowers t ⊔ zpowers z

@[expose] def Asc82Lemma54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec5Ctx G t L S z →
    ∀ g : G, g⁻¹ * z * g ∈ centralizer ({t} : Set G) →
      g⁻¹ * z * g ∈ conjClassIn L z ∨
        ∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * z * g) 6 (-1) 3 α

@[expose] def Asc82Lemma55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec5Ctx G t L S z →
    (∃ h : G, h⁻¹ * t * h = t * z) ∨
      ∀ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) → g⁻¹ * t * g ≠ t →
        ∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * t * g) 6 (-1) 1 α

@[expose] def Asc82Lemma56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec5Ctx G t L S z →
    ∃ r : G, (∃ g : G, g⁻¹ * t * g = r) ∧ ∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α

@[expose] def Asc82Lemma57 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G) (B A : Subgroup G),
    Sec5RCtx G t L S z r B A →
      A = (A ⊓ L) ⊔ zpowers r ∧
        ∀ g : G, g⁻¹ * t * g = r → A = (A ⊓ CFSG.conjugate L g) ⊔ zpowers t

end CFSG.OddStandard.SmallF3.Omega
