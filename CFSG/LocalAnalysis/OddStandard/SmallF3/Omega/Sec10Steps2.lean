module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec109Ctx (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
    (K1 K2 : Subgroup G) (g : G) : Prop extends Sec10Ctx G t L S z K1 K2 where
  norm : g ∈ normalizer (S : Set G)
  not_M : g ∉ secM t S L
  two : IsPGroup 2 (zpowers g)
  swap : g⁻¹ * t * g = t * z
  outer1 : IsOuterOn g (K1 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))
  comm2 : ∀ k ∈ K2, g * k * g⁻¹ * k⁻¹ ∈ oddCoreIn (secK0 t z)
  sq : ∀ k ∈ secK0 t z, g * g * k = k * (g * g)

@[expose] def Asc82Step109A : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
    Sec10Ctx G t L S z K1 K2 → ¬ normalizer (S : Set G) ≤ secM t S L →
      ∃ g : G, Sec109Ctx G t L S z K1 K2 g

@[expose] def Asc82Step109B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G)
    (g : G), Sec109Ctx G t L S z K1 K2 g →
      IsWeaklyClosedWrt (secW t K1 K2) (S ⊔ zpowers g) (centralizer ({z} : Set G))

@[expose] def Asc82Step109W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G)
    (g : G), Sec109Ctx G t L S z K1 K2 g → IsStrClosedModZ t z (secW t K1 K2)

@[expose] def Asc82Step109C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G)
    (g : G), Sec109Ctx G t L S z K1 K2 g → IsStrClosedModZ t z (S ⊔ zpowers g)

@[expose] def Asc82Step109D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G)
    (g : G), Sec109Ctx G t L S z K1 K2 g → IsStrClosedModZ t z (S ⊔ zpowers g) →
      IsI4PlusIn (⊤ : Subgroup G) z

end CFSG.OddStandard.SmallF3.Omega
