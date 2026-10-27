module

public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Blueprint

structure Local27 (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N) : Prop where
  oddCore_bot : CFSG.oddCore N = ⊥
  model : LieModel ↥X .PSL 2 2 2
  t_order : orderOf t = 2
  t_cent : ∀ x ∈ X, x * t = t * x
  X_normal : ∀ g ∈ centralizer ({t} : Set N), ∀ x ∈ X, g * x * g⁻¹ ∈ X
  cent_two : padicValNat 2 (Nat.card ↥(centralizer ({t} : Set N) ⊓ centralizer (X : Set N))) = 1
  not_sylow : padicValNat 2 (Nat.card ↥(centralizer ({t} : Set N))) < padicValNat 2 (Nat.card N)

structure Mod27 (N : Type) [Group N] [Finite N] (X : Subgroup N) : Prop where
  exists_module : ∃ (H : Type) (_ : Group H) (_ : Finite H) (ρ : H →* GL (Fin 8) (ZMod 2))
      (π : H →* N), Function.Injective ρ ∧ Function.Surjective π ∧ π.ker = CFSG.oddCore H ∧
      ∃ Xh : Subgroup H, Xh.map π = X ∧ Disjoint Xh π.ker ∧
        (∀ U : Submodule (ZMod 2) (Fin 8 → ZMod 2),
          (∀ x ∈ Xh, ∀ w ∈ U, ((ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w) ∈ U) →
            Module.finrank (ZMod 2) U = 0 ∨ Module.finrank (ZMod 2) U = 4 ∨
              Module.finrank (ZMod 2) U = 8) ∧
        (∀ x ∈ Xh, orderOf x = 3 → ∀ w : Fin 8 → ZMod 2,
          (ρ x : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = w → w = 0)

structure Out27A (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N) : Prop where
  layer_model : LieModel ↥(layer N) .PSL 2 2 4
  t_not_mem : t ∉ layer N
  X_eq : X = centralizer ({t} : Set N) ⊓ layer N

structure Out27B (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N) : Prop where
  exists_factors : ∃ S₁ S₂ : Subgroup N, LieModel ↥S₁ .PSL 2 2 2 ∧ LieModel ↥S₂ .PSL 2 2 2 ∧
    S₁ ⊔ S₂ = layer N ∧ Disjoint S₁ S₂ ∧ (∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) ∧
    (∀ x ∈ S₁, t * x * t⁻¹ ∈ S₂) ∧ X = centralizer ({t} : Set N) ⊓ layer N

structure OneComp27 (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N) : Prop where
  loc : Local27 N X t
  simple : IsSimpleGroup ↥(layer N)
  nonab : ∃ a b : ↥(layer N), a * b ≠ b * a
  cent_bot : centralizer ((layer N : Subgroup N) : Set N) = ⊥
  X_le : X ≤ layer N

@[expose] def NotL2Odd : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N), OneComp27 N X t → Mod27 N X →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → ¬ LieModel ↥(layer N) .PSL 2 p f

@[expose] def NotL28 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N), OneComp27 N X t →
    ¬ LieModel ↥(layer N) .PSL 2 2 3

@[expose] def NotU33 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N), OneComp27 N X t →
    ¬ LieModel ↥(layer N) .PSU 3 3 1

@[expose] def NotAlt : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N), OneComp27 N X t →
    ∀ n : ℕ, 7 ≤ n → n ≤ 10 → ¬ Nonempty (↥(layer N) ≃* alternatingGroup (Fin n))

@[expose] def NotU42 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N), OneComp27 N X t →
    ¬ LieModel ↥(layer N) .PSp 2 3 1

@[expose] def NotJ2 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N), OneComp27 N X t →
    ¬ NativeSporadic.IsSporadic ↥(layer N) .J2

@[expose] def NotL34 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N), OneComp27 N X t → Mod27 N X →
    ¬ LieModel ↥(layer N) .PSL 3 2 2

@[expose] def CaseAL216 : Prop :=
  ∀ (N : Type) [Group N] [Finite N] (X : Subgroup N) (t : N), OneComp27 N X t →
    LieModel ↥(layer N) .PSL 2 2 4 → Out27A N X t

end CFSG.OddStandard.Seitz77
