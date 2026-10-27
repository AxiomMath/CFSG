module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def IsA7SylowSplit (T : Sylow 2 (Equiv.Perm (Fin 7))) (f : Equiv.Perm (Fin 7)) : Prop :=
  orderOf f = 2 ∧ f.cycleType = {2} ∧ f ∈ (T : Subgroup (Equiv.Perm (Fin 7))) ∧
  (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ⊓ zpowers f = ⊥ ∧
  (∀ x ∈ (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7), x * f = f * x) ∧
  (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) ⊔ zpowers f =
    (T : Subgroup (Equiv.Perm (Fin 7)))

@[expose] def IVK_1_1T : Prop :=
  ∀ T : Sylow 2 (Equiv.Perm (Fin 7)), ∃ f : Equiv.Perm (Fin 7), IsA7SylowSplit T f

@[expose] def IVK_1_1a : Prop :=
  ∀ T : Sylow 2 (Equiv.Perm (Fin 7)),
    IsDihedralOrder ↥((T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) 8

@[expose] def IVK_1_1b : Prop :=
  ∀ (T : Sylow 2 (Equiv.Perm (Fin 7))) (f : Equiv.Perm (Fin 7)), IsA7SylowSplit T f →
    ∀ z ∈ (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7), orderOf z = 2 →
      (∀ x ∈ (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7), x * z = z * x) →
        (f * z).cycleType = {2, 2, 2}

@[expose] def IVK_1_1c_a : Prop :=
  ∀ (T : Sylow 2 (Equiv.Perm (Fin 7))) (f : Equiv.Perm (Fin 7)), IsA7SylowSplit T f →
    Nonempty (↥(centralizer ({f} : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) ≃*
        Equiv.Perm (Fin 5))

@[expose] def IVK_1_1c_b : Prop :=
  ∀ (T : Sylow 2 (Equiv.Perm (Fin 7))) (f : Equiv.Perm (Fin 7)), IsA7SylowSplit T f →
    ∀ (Khat : Type) [Group Khat], IsDoubleCoverOfAlt Khat 7 →
      ∀ (φ : Khat ⧸ center Khat ≃* alternatingGroup (Fin 7)) (α : MulAut Khat),
        (∀ x : Khat, ((φ (QuotientGroup.mk (α x)) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
          f * (φ (QuotientGroup.mk x) : Equiv.Perm (Fin 7)) * f⁻¹) →
        HasSL2Model ↥(fixedSubgroup Khat α) (fun q => q = 5)

@[expose] def IVK_1_1c : Prop := IVK_1_1c_a ∧ IVK_1_1c_b

@[expose] def IVK_1_1d : Prop :=
  (∀ x y : Equiv.Perm (Fin 7), x ∈ alternatingGroup (Fin 7) → y ∈ alternatingGroup (Fin 7) →
    orderOf x = 2 → orderOf y = 2 → ConjUnder (alternatingGroup (Fin 7)) x y) ∧
  ∀ (T : Sylow 2 (Equiv.Perm (Fin 7))) (z : Equiv.Perm (Fin 7)),
    z ∈ (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) → orderOf z = 2 →
    (∀ x ∈ (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7), x * z = z * x) →
      Nonempty (↥(centralizer ({z} : Set (Equiv.Perm (Fin 7)))) ≃*
        DihedralGroup 4 × Equiv.Perm (Fin 3)) ∧
      ∃ X : Subgroup (Equiv.Perm (Fin 7)), Nat.card ↥X = 3 ∧
        X ⊔ (T : Subgroup (Equiv.Perm (Fin 7))) = centralizer ({z} : Set (Equiv.Perm (Fin 7)))

@[expose] def IVK_1_1f : Prop :=
  ∀ U : Subgroup (Equiv.Perm (Fin 7)), U ≤ alternatingGroup (Fin 7) → IsFourSubgroup U →
    Nonempty (↥(normalizer (U : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) ≃*
        Equiv.Perm (Fin 4)) ∨
    ∃ (A X : Subgroup (Equiv.Perm (Fin 7))) (t : Equiv.Perm (Fin 7)),
      normalizer (U : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) = (A ⊔ X) ⊔ zpowers t ∧
      U ≤ A ∧ A ⊓ X = ⊥ ∧ (∀ a ∈ A, ∀ x ∈ X, a * x = x * a) ∧
      (∀ a ∈ A, t * a * t⁻¹ ∈ A) ∧ (∀ x ∈ X, t * x * t⁻¹ ∈ X) ∧
      Nonempty (↥A ≃* alternatingGroup (Fin 4)) ∧ Nonempty (↥(A ⊔ zpowers t) ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty (↥(X ⊔ zpowers t) ≃* Equiv.Perm (Fin 3))

@[expose] def IVK_1_1g : Prop :=
  ∀ u : Equiv.Perm (Fin 7), orderOf u = 2 →
    pRank 2 ↥(centralizer ({u} : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) = 2

@[expose] def IVK_1_1h : Prop :=
  ∀ (T : Sylow 2 (Equiv.Perm (Fin 7))) (f : Equiv.Perm (Fin 7)), IsA7SylowSplit T f →
    ∀ z ∈ (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7), orderOf z = 2 →
      (∀ x ∈ (T : Subgroup (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7), x * z = z * x) →
        Nonempty (↥(centralizer ({f * z} : Set (Equiv.Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) ≃*
          Equiv.Perm (Fin 4))

end CFSG.GH74.GLS.IVK
