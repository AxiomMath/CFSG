module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Aut6WordTable

public section

namespace CFSG.QuasithinUnique.A5.Aut6
open Equiv

abbrev P6 := Equiv.Perm (Fin 6)

abbrev A6 := alternatingGroup (Fin 6)

@[expose] def ev {M : Type*} [Monoid M] (a b : M) : List Bool → M
  | [] => 1
  | false :: w => a * ev a b w
  | true :: w => b * ev a b w

@[expose] def ga' : A6 :=
  ⟨List.formPerm [0, 1, 2, 3, 4], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def gb' : A6 := ⟨List.formPerm [0, 1, 5], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def ga : P6 := (ga' : P6)

@[expose] def gb : P6 := (gb' : P6)

@[expose] def phi (w : P6 → List Bool) (x y : P6) (g : P6) : P6 := ev x y (w g)

@[expose] def IsCand (w : P6 → List Bool) (x y : A6) : Prop :=
  ∀ g : A6, phi w x y ((g : P6) * ga) = phi w x y g * x ∧
    phi w x y ((g : P6) * gb) = phi w x y g * y

@[expose] def IsInv (w : P6 → List Bool) (x y : A6) : Prop :=
  ∀ g : A6, phi w x y (phi w x y g) = g

@[expose] def IsConj (w : P6 → List Bool) (x y : A6) : Prop :=
  ∃ σ : P6, ∀ g : A6, phi w x y g = σ⁻¹ * g * σ

@[expose] def HasFix (w : P6 → List Bool) (x y : A6) : Prop :=
  ∃ a : A6, (a : P6) ^ 5 = 1 ∧ (a : P6) ≠ 1 ∧ phi w x y a = a

@[expose] def key (σ : P6) : ℕ := ∑ i : Fin 6, (σ i).val * 6 ^ i.val

@[expose] def word (g : P6) : List Bool := (List.lookup (key g) wordTab).getD []

instance (x y : A6) : Decidable (IsCand word x y) := by unfold IsCand; infer_instance

instance (x y : A6) : Decidable (IsInv word x y) := by unfold IsInv; infer_instance

instance (x y : A6) : Decidable (IsConj word x y) := by unfold IsConj; infer_instance

instance (x y : A6) : Decidable (HasFix word x y) := by unfold HasFix; infer_instance

end CFSG.QuasithinUnique.A5.Aut6
