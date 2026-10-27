module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Vocab

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def IsOmega7Group {G : Type} [Group G] (L : Subgroup G) : Prop :=
  IsQuasisimple L ∧ LieModel (L ⧸ oddCore L) .POmegaOdd 3 3 1

@[expose] def Asc82ZExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    ∀ S : Subgroup G, IsSylow2Of S (centralizer ({t} : Set G)) → ∃ z : G, Asc82Notation t L S z

@[expose] def Asc82Fact43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      CFSG.inSubgroup CFSG.layer (L ⊓ centralizer ({s} : Set G)) = ⊥ →
        ∃ w : G, IsI4PlusIn L w ∧ w⁻¹ * s ∈ centralizer (L : Set G)

@[expose] def Asc82Fact43Class : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ w w' : G, IsI4PlusIn L w → IsI4PlusIn L w' → w' ∈ conjClassIn L w

structure Sec4BData {G : Type} [Group G] (L P B : Subgroup G) (φ : (Fin 7 → ZMod 2) → G) :
    Prop where
  isMax : IsMaxElemAbelianIn P B
  unique : ∀ B' : Subgroup G, IsMaxElemAbelianIn P B' → B' = B
  card : Nat.card B = 2 ^ 6
  cent : centralizer (B : Set G) ⊓ L = B ⊔ centerIn L
  perm : IsPermModuleVia IsEvenVec φ B (L ⊓ normalizer (B : Set G)) (alternatingGroup (Fin 7))
  type2 : ∀ v, IsEvenVec v → v ≠ 0 → (vecWeight v = 2 ↔ InducesTypeSome L (φ v) 7 1 2 (-1))
  type4 : ∀ v, IsEvenVec v → v ≠ 0 → (vecWeight v = 4 ↔ IsI4PlusIn L (φ v))
  type6 : ∀ v, IsEvenVec v → v ≠ 0 → (vecWeight v = 6 ↔ InducesTypeSome L (φ v) 7 1 6 (-1))
  centK : ∀ v, IsEvenVec v → vecWeight v = 6 → ∀ K : Subgroup G,
    IsComponentIn K (L ⊓ centralizer ({φ v} : Set G)) → φ v ∈ K → IsTwoU43 (K ⧸ oddCore K) →
      centralizer (K : Set G) ⊓ B = zpowers (φ v)

@[expose] def Asc82FactE64 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ P : Subgroup G, IsSylow2Of P L → ∃ (B : Subgroup G) (φ : (Fin 7 → ZMod 2) → G),
      Sec4BData L P B φ

@[expose] def Asc82FactCentB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ P B : Subgroup G, IsSylow2Of P L → IsMaxElemAbelianIn P B → Nat.card B = 2 ^ 6 →
      ∀ x : G, x ∈ normalizer (L : Set G) → (∀ b ∈ B, x * b = b * x) →
        x ∈ B ⊔ centralizer (L : Set G)

@[expose] def Asc82Fact6Class : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ u u' : G, u ∈ L → u' ∈ L → orderOf u = 2 → orderOf u' = 2 →
      InducesTypeSome L u 7 1 6 (-1) → InducesTypeSome L u' 7 1 6 (-1) → u' ∈ conjClassIn L u

@[expose] def Asc82Fact214 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → s ∉ centralizer (L : Set G) →
      (∃ v : G, IsI4PlusIn L v ∧ v ∈ centralizer ({s} : Set G) ∧ s * v ∈ conjClassIn L s) ∨
        ∃ α : ℤˣ, InducesTypeSome L s 7 1 6 α

@[expose] def Asc82FactInner6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → InducesTypeSome L s 7 1 6 (-1) →
      ∃ u c : G, u ∈ L ∧ orderOf u = 2 ∧ InducesTypeSome L u 7 1 6 (-1) ∧
        c ∈ centralizer (L : Set G) ∧ s = u * c

@[expose] def Asc82FactK6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOmega7Group L →
    ∀ u : G, u ∈ L → orderOf u = 2 → InducesTypeSome L u 7 1 6 (-1) →
      ∃ K : Subgroup G, IsComponentIn K (L ⊓ centralizer ({u} : Set G)) ∧ u ∈ K ∧
        IsTwoU43 (K ⧸ oddCore K)

@[expose] def Asc82Split47 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    (¬ ∃ h : G, h⁻¹ * t * h = t * z) → ∀ A : Subgroup G, IsMaxElemAbelianIn (SLC S L) A →
      ∃ M₀ : Subgroup G, M₀ ≤ normalizer (A : Set G) ∧
        M₀.relIndex (normalizer (A : Set G)) = 2 ∧ t ∉ M₀

end CFSG.OddStandard.SmallF3.Omega
