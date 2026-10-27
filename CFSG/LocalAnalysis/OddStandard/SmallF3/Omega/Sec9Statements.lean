module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Asub9 (t t₀ : G) (B : Subgroup G) : Subgroup G :=
  zpowers t ⊔ zpowers t₀ ⊔ B

structure Sec9Choice (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B : Subgroup G) (t₀ : G) : Prop extends Sec9Ctx G t L S z g B t₀ where
  choice : B = Asub9 t t₀ B ⊓ CFSG.conjugate L g

@[expose] def Asc82Lemma91 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G)
    (t₀ : G), Sec9Ctx G t L S z g B t₀ →
      ∃ (B' : Subgroup G) (t₀' : G), Sec9Choice G t L S z g B' t₀'

@[expose] def Asc82Lemma9N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G)
    (t₀ : G), Sec9Choice G t L S z g B t₀ →
      (L ⊓ normalizer (Asub9 t t₀ B : Set G)) ⊔
          (CFSG.conjugate L g ⊓ normalizer (Asub9 t t₀ B : Set G)) ≤ centMod (Asub9 t t₀ B) B ∧
        IsSylow2Of (Asub9 t t₀ B) (centralizer (Asub9 t t₀ B : Set G)) ∧
        IsSylow2Of (Asub9 t t₀ B) (centralizer ((zpowers t ⊔ B : Subgroup G) : Set G)) ∧
        centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) =
          centMod (Asub9 t t₀ B) B ⊓ centralizer ((zpowers t ⊔ B : Subgroup G) : Set G) ∧
        centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) =
          oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B ∧
        ConjTwoTransOn (centMod (Asub9 t t₀ B) B) (cosetSet t B)

structure Sec9E1 (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G)
    (B : Subgroup G) (t₀ : G) (E1 : Subgroup G) : Prop where
  choice : Sec9Choice G t L S z g B t₀
  A_le : Asub9 t t₀ B ≤ E1
  le_N : E1 ≤ centMod (Asub9 t t₀ B) B
  quot : QuotEquivTo E1 (Asub9 t t₀ B) E16
  normal : ((E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)).subgroupOf
    (centMod (Asub9 t t₀ B) B)).Normal
  top : QuotEquivTo (centMod (Asub9 t t₀ B) B)
      (E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)) (alternatingGroup (Fin 6)) ∨
    QuotEquivTo (centMod (Asub9 t t₀ B) B)
      (E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)) (Equiv.Perm (Fin 6))

@[expose] def Asc82Fink9E1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z g : G) (B : Subgroup G)
    (t₀ : G), Sec9Choice G t L S z g B t₀ → ∃ E1 : Subgroup G, Sec9E1 G t L S z g B t₀ E1

end CFSG.OddStandard.SmallF3.Omega
