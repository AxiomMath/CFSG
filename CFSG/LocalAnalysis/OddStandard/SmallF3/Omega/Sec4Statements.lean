module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Vocab

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma41 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec4Setting G t L → InCStar L

@[expose] def Asc82Lemma42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec4Setting G t L →
    ∀ P : Sylow 2 (centralizer (L : Set G)), IsCyclic (P : Subgroup (centralizer (L : Set G)))

@[expose] def Asc82Lemma43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∀ g : G, g⁻¹ * z * g ∈ centralizer ({t} : Set G) →
      g⁻¹ * z * g ∈ conjClassIn L z ∨ g⁻¹ * z * g ∈ conjClassIn L (t * z)

@[expose] def Asc82Lemma44d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∀ A : Subgroup G, IsMaxElemAbelianIn (SLC S L) A →
      A ⊓ L = Subgroup.closure (conjClassIn (L ⊓ normalizer (A : Set G)) z)

@[expose] def Asc82Lemma46a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∀ A : Subgroup G, IsMaxElemAbelianIn (SLC S L) A →
      ((∃ g : G, g⁻¹ * z * g = t * z) ∧
          A = Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G))) ∨
        (conjClassIn ⊤ z ∩ (centralizer ({t} : Set G) : Set G) = conjClassIn L z ∧
          A ⊓ L = Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G)))

@[expose] def Asc82Lemma46b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∀ A : Subgroup G, IsMaxElemAbelianIn (SLC S L) A →
      (∀ g : G, CFSG.conjugate A g ≤ S → CFSG.conjugate A g = A) ∧
        conjClassIn ⊤ t ∩ (A : Set G) = conjClassIn (normalizer (A : Set G)) t

@[expose] def Asc82Lemma47 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∃ h : G, h⁻¹ * t * h = t * z

@[expose] def Asc82Lemma48a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    conjClassIn ⊤ z ∩ (centralizer ({t} : Set G) : Set G) = conjClassIn L z

@[expose] def Asc82Lemma48b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∀ A : Subgroup G, IsMaxElemAbelianIn (SLC S L) A →
      A ⊓ L = Subgroup.closure (conjClassIn ⊤ z ∩ (A : Set G)) ∧
        ∀ m ∈ normalizer (A : Set G), ∀ b ∈ A ⊓ L, m * b * m⁻¹ ∈ A ⊓ L

@[expose] def Asc82Lemma49 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∀ A : Subgroup G, IsMaxElemAbelianIn (SLC S L) A →
      ∀ u : G, u ∈ A ⊓ L → orderOf u = 2 → InducesTypeSome L u 7 1 6 (-1) →
        (∀ m ∈ normalizer (A : Set G), m * u = u * m → m * t = t * m) ∨
          ((∃ h : G, h⁻¹ * t * h = t * u) ∧
            ∀ m ∈ normalizer (A : Set G), m * u = u * m →
              m ∈ normalizer ((zpowers u ⊔ zpowers t : Subgroup G) : Set G))

@[expose] def Asc82Lemma410Ctx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z → False

end CFSG.OddStandard.SmallF3.Omega
