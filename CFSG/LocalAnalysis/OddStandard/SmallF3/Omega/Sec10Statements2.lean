module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Asc82Lemma107a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 →
      ∃ φ : (Fin 5 → ZMod 2) → G,
        IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L) (alternatingGroup (Fin 5))

@[expose] def Asc82Lemma107b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 →
      Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
        Nonempty (↥(autIn (secCMt t S L) (secA t S L)) ≃* Equiv.Perm (Fin 5))

@[expose] def Asc82Lemma107c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 →
      secA t S L = JElem S ∨
        ∃ r ∈ S, orderOf r = 2 ∧ InducesTypeSome L r 5 1 4 (-1) ∧
          secA2 t r K1 K2 ≠ secA t S L ∧
          ∀ X : Subgroup G, IsNormalE32In S X ↔ (X = secA t S L ∨ X = secA2 t r K1 K2)

@[expose] def Asc82Lemma108 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → ∀ g : G, g⁻¹ * t * g ∉ L

@[expose] def Asc82Lemma109 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → normalizer (S : Set G) ≤ secM t S L

@[expose] def Asc82Lemma1010 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 →
      (∀ m ∈ secM t S L, ∀ b ∈ secB S L, m * b * m⁻¹ ∈ secB S L) ∧
        ∀ g : G, g⁻¹ * t * g ∈ secA t S L → g⁻¹ * t * g ∈ secTB t S L

@[expose] def Sec1011Alt1 (t : G) (S L : Subgroup G) : Prop :=
  conjClassIn ⊤ t ∩ (secA t S L : Set G) = secTB t S L ∧
    secTB t S L = conjClassIn (secM t S L) t ∧
    secMstar t S L = autIn (secCMB t S L) (secA t S L) ⊔ autIn (secCMt t S L) (secA t S L) ∧
    (autIn (secCMB t S L) (secA t S L)).subgroupOf (secMstar t S L) =
      CFSG.pCore 2 ↥(secMstar t S L) ∧
    IsElemAb2 (autIn (secCMB t S L) (secA t S L)) 4 ∧
    ∀ x y : ↥(secA t S L), (x : G) ∈ secTB t S L → (y : G) ∈ secTB t S L →
      ∃! c : ↥(autIn (secCMB t S L) (secA t S L)), (c : MulAut ↥(secA t S L)) x = y

@[expose] def Sec1011Alt2 (t : G) (S L : Subgroup G) (z : G) : Prop :=
  Hyp111 t S L ∧ conjClassIn ⊤ t ∩ (secA t S L : Set G) = conjClassIn (secM t S L) t ∧
    conjClassIn (secM t S L) t = {t} ∪ conjClassIn (secM t S L ⊓ L) (t * z) ∧
    (conjClassIn (secM t S L) t).ncard = 6 ∧
    (IsPermMod6 (secA t S L) (secM t S L) (alternatingGroup (Fin 6)) ∨
      IsPermMod6 (secA t S L) (secM t S L) ⊤)

@[expose] def Asc82Lemma1011 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → Sec1011Alt1 t S L ∨ Sec1011Alt2 t S L z

end CFSG.OddStandard.SmallF3.Omega
