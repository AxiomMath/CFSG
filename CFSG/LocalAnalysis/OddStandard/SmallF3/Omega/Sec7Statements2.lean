module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Lemma77a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec7Choice G t L S z g B →
      IsElemAb2 (ASub S B ⊓ CFSG.conjugate L g) 4 ∧
        QuotEquivTo (CFSG.conjugate L g ⊓ MSub S B) (CFSG.conjugate L g ⊓ ASub S B)
          (Equiv.Perm (Fin 5))

@[expose] def Asc82Lemma77b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec7Choice G t L S z g B →
      ∃ n ∈ CFSG.conjugate L g ⊓ MSub S B, t * n ≠ n * t

@[expose] def Asc82Lemma78 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec7Choice G t L S z g B → ASub S B = zpowers t ⊔ B

@[expose] def Asc82Lemma79a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec7Choice G t L S z g B → Hyp62At L

@[expose] def Asc82Lemma710a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec7Choice G t L S z g B → g⁻¹ * t * g = t * z

@[expose] def Asc82Lemma710b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec7Choice G t L S z g B →
      {x : G | IsConj z x} ∩ (centralizer ({t} : Set G) : Set G) = conjClassIn L z

@[expose] def Asc82Lemma710c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec7Choice G t L S z g B →
      B = ASub S B ⊓ L ∧
        B = Subgroup.closure ({x : G | IsConj z x} ∩ (ASub S B : Set G)) ∧
        (B.subgroupOf (MSub S B)).Normal

@[expose] def Asc82Lemma710d : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G),
    Sec7Choice G t L S z g B →
      MSub S B = (MSub S B ⊓ centralizer (B : Set G)) ⊔ (L ⊓ MSub S B) ∧
        (∀ N : Subgroup G, N ≤ MSub S B → (N.subgroupOf (MSub S B)).Normal →
          centralizer (ASub S B : Set G) ≤ N →
          (∃ k : ℕ, (centralizer (ASub S B : Set G)).relIndex N = 2 ^ k) →
            N ≤ centralizer (B : Set G)) ∧
        QuotEquivTo (MSub S B ⊓ centralizer (B : Set G)) (centralizer (ASub S B : Set G)) E16 ∧
        cosetSet t B ⊆ {x : G | IsConj t x} ∩ (ASub S B : Set G) ∧
        (∀ x ∈ cosetSet t B, ∀ y ∈ cosetSet t B,
          ∃ n ∈ MSub S B ⊓ centralizer (B : Set G), n * x * n⁻¹ = y) ∧
        (∀ n ∈ MSub S B ⊓ centralizer (B : Set G), ∀ x ∈ cosetSet t B,
          n * x * n⁻¹ = x → n ∈ centralizer (ASub S B : Set G))

end CFSG.OddStandard.SmallF3.Omega
