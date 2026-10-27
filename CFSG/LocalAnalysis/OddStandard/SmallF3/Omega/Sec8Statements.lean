module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Asub8 (t : G) (B : Subgroup G) : Subgroup G :=
  zpowers t ⊔ B

@[expose] def Nsub8 (t : G) (B : Subgroup G) : Subgroup G :=
  normalizer ((Asub8 t B : Subgroup G) : Set G)

@[expose] def Asc82Lemma81 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Minus L → InCStar L

@[expose] def Asc82Lemma82 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Minus L → ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic P

@[expose] def Asc82Lemma83 : Prop :=
  Asc82Lemma66

@[expose] def Asc82Thm84 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    IsOmega6Minus L → ∃ s : G, orderOf s = 2 ∧ s ∈ centralizer ({t} : Set G) ∧
      ∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α

@[expose] def Asc82Lemma84Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B →
      {x : G | IsConj z x} ∩ (centralizer ({t} : Set G) : Set G) = conjClassIn L z

@[expose] def Asc82Lemma85 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B → S ⊓ L = S ⊓ CFSG.conjugate L g

@[expose] def Asc82Lemma86 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B → S ⊓ centralizer (L : Set G) = zpowers t

@[expose] def Asc82Lemma87 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B → ∀ y : G, ∀ α : ℤˣ,
      ¬ InducesTypeSome L y 6 (-1) 1 α ∧ ¬ InducesTypeSome L y 6 (-1) 3 α

@[expose] def Asc82Lemma8A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B →
      Asub8 t B ⊔ oddCoreIn (Nsub8 t B) = normalizer (L : Set G) ⊓ centralizer (Asub8 t B : Set G) ∧
        normalizer (L : Set G) ⊓ centralizer (Asub8 t B : Set G) =
          centralizer (Asub8 t B : Set G)

@[expose] def Asc82Lemma8B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec8Ctx G t L S z g B →
      ConjTwoTransOn (Nsub8 t B) (cosetSet t B) ∧
        cosetSet t B = {x : G | IsConj t x} ∩ (Asub8 t B : Set G)

end CFSG.OddStandard.SmallF3.Omega
