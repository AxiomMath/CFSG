module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec4AData {G : Type} [Group G] (t : G) (L S : Subgroup G) (z : G) (A B : Subgroup G)
    (φ : (Fin 7 → ZMod 2) → G) : Prop where
  bdata : Sec4BData L (S ⊓ L) B φ
  isMax : IsMaxElemAbelianIn (SLC S L) A
  unique : ∀ A' : Subgroup G, IsMaxElemAbelianIn (SLC S L) A' → A' = A
  A_eq : A = B ⊔ zpowers t
  B_eq : A ⊓ L = B
  centB : ∀ x ∈ S, (∀ b ∈ B, x * b = b * x) → x ∈ SLC S L
  z_eq : ∃ v, IsEvenVec v ∧ vecWeight v = 4 ∧ φ v = z

@[expose] def Asc82ADataExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∃ (A B : Subgroup G) (φ : (Fin 7 → ZMod 2) → G), Sec4AData t L S z A B φ

@[expose] def Asc82Lemma44e : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G), Sec4Ctx G t L S z →
    ∀ A : Subgroup G, IsMaxElemAbelianIn (SLC S L) A →
      t ∈ A ∧ z ∈ A ∧ A = (A ⊓ L) ⊔ zpowers t ∧ Nat.card ↥(A ⊓ L) = 2 ^ 6

end CFSG.OddStandard.SmallF3.Omega
