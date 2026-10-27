module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma120 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E →
      (secA t S L ≤ E ∧ E ⊓ centralizer (secA t S L : Set G) = secA t S L) ∧
      ((∀ e ∈ E, ∀ e' ∈ E, e * e' * e⁻¹ * e'⁻¹ ∈ secA t S L) ∧
        (∀ e ∈ E, e * e ∈ secA t S L) ∧ (secA t S L).relIndex E = 16) ∧
      autIn (secM t S L ⊓ normalizer (E : Set G)) (secA t S L) = secMstar t S L ∧
      ((∀ e ∈ E, e * t * e⁻¹ * t⁻¹ ∈ secB S L) ∧
        (∀ b ∈ secB S L, ∃ e ∈ E, e * t * e⁻¹ * t⁻¹ = b) ∧
        (∀ e ∈ E, e * t * e⁻¹ * t⁻¹ = 1 ↔ e ∈ secA t S L)) ∧
      IsNatModA5 E (secA t S L) (secM t S L ⊓ L) ∧
      ((∀ e ∈ E, ∀ e' ∈ E, e * e' * e⁻¹ * e'⁻¹ ∈ secB S L) ∧
        (∀ e ∈ E, e * e ∈ secB S L) ∧ (secB S L).relIndex E = 32)

@[expose] def Asc82Lemma121 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E →
      (IsElemAb2 (secV t S L E) 8 ∨ IsZ4Pow4 (secV t S L E)) ∧
      secV t S L E ⊔ zpowers t = E ∧ secV t S L E ⊓ zpowers t = ⊥ ∧
      E ≤ normalizer (secV t S L E : Set G) ∧
      Nonempty (↥(autIn (secM t S L ⊓ L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∧
      (∃ φ : (Fin 5 → ZMod 2) → G,
        IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5))) ∧
      IsNatModA5 (secV t S L E) (secB S L) (secM t S L ⊓ L)

@[expose] def Asc82Lemma122 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → ∃ X : Subgroup G, Sec12X t S L E X

@[expose] def Asc82Lemma123 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E X : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → Sec12X t S L E X →
      Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) ∧
      X ⊓ centralizer (secA t S L : Set G) = ⊥ ∧
      autIn X (secA t S L) = autIn (secCMt t S L) (secA t S L) ∧
      Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5)))

@[expose] def Asc82Lemma124 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E → IsElemAb2 (secV t S L E) 8

@[expose] def Asc82Lemma125a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E →
      centralizer (secV t S L E : Set G) = secV t S L E ⊔ oddCoreIn (secN (secV t S L E))

@[expose] def Asc82Lemma125b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 E : Subgroup G),
    Sec12Ctx G t L S z K1 K2 E →
      secNb (secV t S L E) ⊓ Subgroup.centralizer {betaOf (secV t S L E) t} =
        autIn (secN (secV t S L E) ⊓ centralizer ({t} : Set G)) (secV t S L E) ∧
      Nonempty (↥(autIn (secN (secV t S L E) ⊓ centralizer ({t} : Set G)) (secV t S L E)) ≃*
        (Multiplicative (ZMod 2) × ↥(alternatingGroup (Fin 5))))

end CFSG.OddStandard.SmallF3.Omega
