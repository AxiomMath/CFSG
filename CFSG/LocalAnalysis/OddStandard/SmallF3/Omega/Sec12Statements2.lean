module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma126 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E →
      ∀ h : G, h⁻¹ * t * h ∈ secN (secV t S L E) →
        (∃ c ∈ centralizer ({h⁻¹ * t * h} : Set G),
          secV t S L E ⊓ centralizer ({h⁻¹ * t * h} : Set G) =
            CFSG.conjugate (CFSG.conjugate (secB S L) h) c) ∧
        ∃ n ∈ secN (secV t S L E), n⁻¹ * t * n = h⁻¹ * t * h

@[expose] def Asc82Lemma127 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E X : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → Sec12X t S L E X →
      ∀ y : MulAut ↥(secV t S L E),
        ((∃ b ∈ secNb (secV t S L E), y = b * betaOf (secV t S L E) t * b⁻¹) ∧
            y ∈ Subgroup.centralizer {betaOf (secV t S L E) t}) ↔
          ((∃ x ∈ autIn X (secV t S L E), y = betaOf (secV t S L E) t * x) ∧ y * y = 1 ∧
            y ≠ 1)

@[expose] def Asc82Lemma128 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E X : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → Sec12X t S L E X →
      Sec128Alt1 t S L (secV t S L E) ∨ Sec128Alt2 (secV t S L E)

@[expose] def Asc82Lemma129 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E →
      ∀ R0 : Subgroup G, S ≤ R0 → IsSylow2Of R0 (secN (secV t S L E)) →
        JElem R0 = secV t S L E ∧ IsSylow2Of R0 ⊤

@[expose] def Asc82Lemma1210 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → t ∉ oTwoRes (⊤ : Subgroup G)

end CFSG.OddStandard.SmallF3.Omega
