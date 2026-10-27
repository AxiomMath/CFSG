module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec128Coord {V : Type} [Group V] (V1 : Subgroup V) (φ : (Fin 5 → ZMod 2) → V) :
    Prop where
  mem : ∀ v, IsEvenVec v → φ v ∈ V1
  mul : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w
  inj : ∀ v, IsEvenVec v → φ v = 1 → v = 0
  surj : ∀ x ∈ V1, ∃ v, IsEvenVec v ∧ φ v = x

@[expose] def Sec128SplitNatOn {G : Type} [Group G] (V : Subgroup G) (Z : Subgroup (MulAut ↥V))
    (V1 V2 : Subgroup ↥V) : Prop :=
  ∃ (φ1 φ2 : (Fin 5 → ZMod 2) → ↥V)
    (ψ : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) ≃* ↥Z),
    V1 ⊔ V2 = ⊤ ∧ V1 ⊓ V2 = ⊥ ∧ Sec128Coord V1 φ1 ∧ Sec128Coord V2 φ2 ∧
      ∀ (a b : ↥(alternatingGroup (Fin 5))) (v : Fin 5 → ZMod 2), IsEvenVec v →
        (ψ (a, b) : MulAut ↥V) (φ1 v) = φ1 (permVec (a : Equiv.Perm (Fin 5)) v) ∧
          (ψ (a, b) : MulAut ↥V) (φ2 v) = φ2 (permVec (b : Equiv.Perm (Fin 5)) v)

@[expose] def Sec128SplitNat {G : Type} [Group G] (V : Subgroup G) (Z : Subgroup (MulAut ↥V)) :
    Prop :=
  ∃ V1 V2 : Subgroup ↥V, Sec128SplitNatOn V Z V1 V2

@[expose] def Sec128WrNat {G : Type} [Group G] (V : Subgroup G) (Y : Subgroup (MulAut ↥V)) :
    Prop :=
  ∃ (Z : Subgroup (MulAut ↥V)) (V1 V2 : Subgroup ↥V) (τ : MulAut ↥V),
    Z ≤ Y ∧ (Z.subgroupOf Y).index = 2 ∧ Sec128SplitNatOn V Z V1 V2 ∧ τ ∈ Y ∧ τ ∉ Z ∧
      V1.map (τ : ↥V ≃* ↥V).toMonoidHom = V2

@[expose] def Asc82S8NoL34X : Prop :=
  ∀ (G : Type) [Group G] (V X V1 V2 : Subgroup G) (Z : Subgroup (MulAut ↥V)),
    IsElemAb2 V 8 → V1 ⊔ V2 = V → V1 ⊓ V2 = ⊥ → Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) →
    IsNatModA5 V1 ⊥ X → IsNatModA5 V2 ⊥ X → autIn X V ≤ Z → ¬ LieModel ↥Z .PSL 3 2 2

@[expose] def Asc82S8NoL216 : Prop :=
  ∀ (G : Type) [Group G] (V X V1 V2 : Subgroup G) (Z : Subgroup (MulAut ↥V)),
    IsElemAb2 V 8 → V1 ⊔ V2 = V → V1 ⊓ V2 = ⊥ → Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) →
    IsNatModA5 V1 ⊥ X → IsNatModA5 V2 ⊥ X → autIn X V ≤ Z → ¬ LieModel ↥Z .PSL 2 2 4

@[expose] def Asc82S8Dich : Prop :=
  ∀ (G : Type) [Group G] (V X V1 V2 : Subgroup G) (Z : Subgroup (MulAut ↥V)),
    IsElemAb2 V 8 → V1 ⊔ V2 = V → V1 ⊓ V2 = ⊥ → Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) →
    IsNatModA5 V1 ⊥ X → IsNatModA5 V2 ⊥ X → autIn X V ≤ Z →
    Nonempty (↥Z ≃* (↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))) →
      Sec128SplitNat V Z ∨ IsNatOmega4Plus V Z

@[expose] def Asc82S8Split : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Subgroup G), IsElemAb2 V 8 →
    centralizer (V : Set G) = V ⊔ oddCoreIn (normalizer (V : Set G)) →
    Sec128WrNat V (autIn (normalizer (V : Set G)) V) →
      ∃ K : Subgroup G, K ≤ normalizer (V : Set G) ∧ oddCoreIn (normalizer (V : Set G)) ≤ K ∧
        K ⊓ V = ⊥ ∧ K ⊔ V = normalizer (V : Set G)

end CFSG.OddStandard.SmallF3.Omega
