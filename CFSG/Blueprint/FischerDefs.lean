module

public import CFSG.Blueprint.NativeSporadic

public noncomputable section

namespace CFSG.Blueprint.Fischer

abbrev K := GaloisField 2 2
abbrev V := Fin 6 → K

@[expose] def hermitian (H : Matrix (Fin 6) (Fin 6) K) (x y : V) : K :=
  ∑ i, ∑ j, x i * H i j * (y j) ^ 2

@[expose] def IsNondegenerateHermitian (H : Matrix (Fin 6) (Fin 6) K) : Prop :=
  (∀ i j, H j i = (H i j) ^ 2) ∧
    ∀ x : V, (∀ y : V, hermitian H x y = 0) → x = 0

@[expose] def SU (H : Matrix (Fin 6) (Fin 6) K) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 6) K) :=
  Subgroup.closure {g | Matrix.GeneralLinearGroup.det g = 1 ∧
    ∀ x y : V, hermitian H (Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) K) x)
      (Matrix.mulVec (g : Matrix (Fin 6) (Fin 6) K) y) = hermitian H x y}

abbrev PSU (H : Matrix (Fin 6) (Fin 6) K) := SU H ⧸ Subgroup.center (SU H)

@[expose] def Transvections (H : Matrix (Fin 6) (Fin 6) K) : Set (PSU H) :=
  {g | ∃ u : SU H, QuotientGroup.mk u = g ∧ ∃ v : V, v ≠ 0 ∧ hermitian H v v = 0 ∧
    ∀ x : V, Matrix.mulVec ((u : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) x =
      x + hermitian H x v • v}

@[expose] def Pair (X : Type) [Group X] (E : Set X) : Prop :=
  Finite X ∧ (∃ e : X, E = {x | IsConj e x}) ∧
    (∀ e ∈ E, orderOf e = 2) ∧
    (∀ e ∈ E, ∀ f ∈ E, orderOf (e * f) ∈ ({1, 2, 3} : Set ℕ)) ∧
    Subgroup.closure E = ⊤

@[expose] def LocalClass {X : Type} [Group X] (E : Set X) (e : X) : Set X :=
  {f | f ∈ E ∧ f ≠ e ∧ f * e = e * f}

@[expose] def LocalGroup {X : Type} [Group X] (E : Set X) (e : X) : Subgroup X :=
  Subgroup.closure (LocalClass E e)

abbrev LocalQuotient {X : Type} [Group X] (E : Set X) (e : X) :=
  LocalGroup E e ⧸ Subgroup.center (LocalGroup E e)

@[expose] def LocalImages {X : Type} [Group X] (E : Set X) (e : X) : Set (LocalQuotient E e) :=
  {q | ∃ f : LocalGroup E e, (f : X) ∈ LocalClass E e ∧ QuotientGroup.mk f = q}

@[expose] def F22 (X : Type) [Group X] (E : Set X) : Prop :=
  Pair X E ∧ ∃ e ∈ E, ∃ H : Matrix (Fin 6) (Fin 6) K, IsNondegenerateHermitian H ∧
    ∃ iso : LocalQuotient E e ≃* PSU H, iso '' LocalImages E e = Transvections H

@[expose] def F23 (X : Type) [Group X] (E : Set X) : Prop :=
  Pair X E ∧ ∃ e ∈ E, F22 (LocalQuotient E e) (LocalImages E e)

@[expose] def F24 (X : Type) [Group X] (E : Set X) : Prop :=
  Pair X E ∧ ∃ e ∈ E, F23 (LocalQuotient E e) (LocalImages E e)

@[expose] def HasType (k : Fin 3) (X : Type) [Group X] (E : Set X) : Prop :=
  match k.val with
  | 0 => F22 X E
  | 1 => F23 X E
  | _ => F24 X E

@[expose] def Carrier (k : Fin 3) : Type :=
  match k.val with
  | 0 => NativeSporadic.Fi22
  | 1 => NativeSporadic.Fi23
  | _ => MulAut NativeSporadic.Fi24prime

instance carrierGroup (k : Fin 3) : Group (Carrier k) := by
  unfold Carrier
  split <;> infer_instance

@[expose] def LocalStructure (k : Fin 3) (D : Set (Carrier k)) : Prop :=
  ∀ d ∈ D, let C := Subgroup.centralizer ({d} : Set (Carrier k))
    (k.val = 0 → commutator C = ⊤ ∧
      (Subgroup.center C).map C.subtype = Subgroup.zpowers d ∧ Nat.card (Subgroup.center C) = 2 ∧
      ∃ H : Matrix (Fin 6) (Fin 6) K, IsNondegenerateHermitian H ∧
        Nonempty ((C ⧸ Subgroup.center C) ≃* PSU H)) ∧
    (k.val = 1 → commutator C = ⊤ ∧
      (Subgroup.center C).map C.subtype = Subgroup.zpowers d ∧ Nat.card (Subgroup.center C) = 2 ∧
      Nonempty ((C ⧸ Subgroup.center C) ≃* NativeSporadic.Fi22)) ∧
    (k.val = 2 → ∃ L : Subgroup (Carrier k), Nonempty (L ≃* NativeSporadic.Fi23) ∧
      C = Subgroup.zpowers d ⊔ L ∧ Subgroup.zpowers d ⊓ L = ⊥ ∧
      Subgroup.zpowers d ≤ Subgroup.centralizer (L : Set (Carrier k)))

end CFSG.Blueprint.Fischer
