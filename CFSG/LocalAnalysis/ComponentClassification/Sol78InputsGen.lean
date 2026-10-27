module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Foundations.Basic

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup

@[expose] def layerOfFixed {G : Type*} [Group G] (s : MulAut G) : Subgroup G :=
  (CFSG.pLayer ↥(Open.signalizerFixedSubgroup s) 2).map (Open.signalizerFixedSubgroup s).subtype

@[expose] def IsTripleCoverAltSeven {G : Type*} [Group G] (L : Subgroup G) : Prop :=
  ⁅L, L⁆ = L ∧ Nat.card (center L) = 3 ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7))

@[expose] def HeldGenerationInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.He) →
    ∀ s : MulAut G, orderOf s = 2 → ∀ m : ℕ,
    (Nonempty (layerOfFixed s ≃* alternatingGroup (Fin m)) ∨
      IsTripleCoverAltSeven (layerOfFixed s)) →
    ∀ (e : layerOfFixed s ⧸ pPrimeCore 2 (layerOfFixed s) ≃* alternatingGroup (Fin m))
      (F : Subgroup G), F ≤ layerOfFixed s →
      Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
      (∃ D : Finset (Fin m), D.card = 4 ∧ ∀ x : layerOfFixed s, (x : G) ∈ F → ∀ ω ∉ D,
        ((e (x : layerOfFixed s ⧸ pPrimeCore 2 (layerOfFixed s)) : alternatingGroup (Fin m)) :
          Equiv.Perm (Fin m)) ω = ω) →
      layerOfFixed s ⊔ normalizer (F : Set G) = ⊤

end CFSG.ComponentClassification.Sol78
