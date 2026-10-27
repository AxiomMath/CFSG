module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Bundles
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def secXH {G : Type} [Group G] (t z : G) : Subgroup G :=
  Subgroup.closure {s | ∃ h ∈ centralizer ({z} : Set G), s = h⁻¹ * t * h}

structure Asc82Pre11 : Prop where
  s3 : Asc82Sec3Res10
  r10 : Asc82Res10
  facts : Asc82Facts10
  basic : Asc82Basic10

structure Asc82Res11a : Prop where
  l111N : Asc82Lemma111N
  l112 : Asc82Lemma112
  l113 : Asc82Lemma113
  l114 : Asc82Lemma114
  l115b : Asc82Lemma115b
  l115c : Asc82Lemma115c
  l115d : Asc82Lemma115d

structure Asc82Res11 : Prop extends Asc82Res11a where
  l116 : Asc82Lemma116
  l117 : Asc82Lemma117
  l118 : Asc82Lemma118
  l119 : Asc82Lemma119
  l1110 : Asc82Lemma1110
  l1111 : Asc82Lemma1111

@[expose] def Asc82Step111T : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → Hyp111 t S L → IsSylow2Of T (secM t S L) → S ≤ T →
      S.relIndex T = 2 ∧ conjClassIn T t = {t, t * z} ∧
        T ≤ normalizer (secK0 t z : Set G) ∧ T ≤ normalizer (secQ K1 K2 : Set G)

@[expose] def Asc82Step111TR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → Hyp111 t S L → ∃ T R : Subgroup G, Sec11Ctx G t L S z K1 K2 T R

@[expose] def Asc82Step1111X : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R → ∃ P : Subgroup G, IsSylow2Of P (secXH t z) ∧ IsDihSd P

@[expose] def Asc82Step1111K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G),
    Sec11Ctx G t L S z K1 K2 T R →
      (∃ P : Subgroup G, IsSylow2Of P (secXH t z) ∧ IsDihSd P) →
        centralizer ({z} : Set G) ≤
          normalizer ((K1 ⊔ K2 ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G)

@[expose] def Asc82StepPocketOfNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 →
      centralizer ({z} : Set G) ≤
        normalizer ((K1 ⊔ K2 ⊔ oddCoreIn (centralizer ({z} : Set G)) : Subgroup G) : Set G) →
        IsI4PlusIn (⊤ : Subgroup G) z

end CFSG.OddStandard.SmallF3.Omega
