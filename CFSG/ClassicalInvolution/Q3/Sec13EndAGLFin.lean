module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13.AGLFin

open scoped commutatorElement

@[expose] def planes : List (Finset (Fin 8)) :=
  [{0, 2, 4, 6}, {1, 3, 5, 7}, {0, 1, 4, 5}, {2, 3, 6, 7}, {0, 3, 4, 7}, {1, 2, 5, 6},
    {0, 1, 2, 3}, {4, 5, 6, 7}, {0, 2, 5, 7}, {1, 3, 4, 6}, {0, 1, 6, 7}, {2, 3, 4, 5},
    {0, 3, 5, 6}, {1, 2, 4, 7}]

@[expose] def trFun (c x : Fin 8) : Fin 8 := ⟨(x.val ^^^ c.val) % 8, Nat.mod_lt _ (by norm_num)⟩

theorem trFun_trFun : ∀ c x : Fin 8, trFun c (trFun c x) = x := by decide +kernel

@[expose] def tr (c : Fin 8) : Equiv.Perm (Fin 8) where
  toFun := trFun c
  invFun := trFun c
  left_inv := trFun_trFun c
  right_inv := trFun_trFun c

@[expose] def lin₁ : Equiv.Perm (Fin 8) := c[4, 5] * c[6, 7]

@[expose] def lin₂ : Equiv.Perm (Fin 8) := c[1, 2, 4] * c[3, 6, 5]

@[expose] def gen₁ (c : Fin 8) : Equiv.Perm (Fin 8) := tr c * lin₁

@[expose] def gen₂ (c : Fin 8) : Equiv.Perm (Fin 8) := tr c * lin₂

@[expose] def vact (s : Equiv.Perm (Fin 8)) (v : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun i => v (s.symm i)

@[expose] def allOnes : Fin 8 → ZMod 2 := fun _ => 1

@[expose] def ind (α : Finset (Fin 8)) : Fin 8 → ZMod 2 := fun i => if i ∈ α then 1 else 0

@[expose] def rmList : List (Fin 8 → ZMod 2) := [0, allOnes] ++ planes.map ind

@[expose] def pol (f : Equiv.Perm (Fin 8)) (v : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  vact (f ^ 3) v + vact f v + v

@[expose] def IsT (f : Equiv.Perm (Fin 8)) (v : Fin 8 → ZMod 2) : Prop :=
  pol f v = 0 ∨ pol f v = allOnes

instance (f : Equiv.Perm (Fin 8)) (v : Fin 8 → ZMod 2) : Decidable (IsT f v) := by
  unfold IsT; infer_instance

@[expose] def Hyp (c₁ c₂ : Fin 8) : Prop :=
  gen₁ c₁ * gen₁ c₁ = 1 ∧ gen₂ c₂ ^ 3 = 1 ∧ (gen₁ c₁ * gen₂ c₂) ^ 7 = 1 ∧
    ⁅gen₁ c₁, gen₂ c₂⁆ ^ 4 = 1 ∧ ∀ x, gen₁ c₁ x ≠ x ∨ gen₂ c₂ x ≠ x

instance (c₁ c₂ : Fin 8) : Decidable (Hyp c₁ c₂) := by unfold Hyp; infer_instance

@[expose] def Concl (c₁ c₂ : Fin 8) : Prop :=
  let f := gen₁ c₁ * gen₂ c₂
  (∀ v, IsT f v → ∑ i, v i = 0) ∧ (Finset.univ.filter (IsT f)).card = 16 ∧
    (∀ v, IsT f v → v ∈ rmList → v = 0 ∨ v = allOnes) ∧
    (∀ v, IsT f v → IsT f (vact (gen₁ c₁) v) ∧ IsT f (vact (gen₂ c₂) v)) ∧
    (∀ v : Fin 8 → ZMod 2, ∑ i, v i = 0 → ∃ r ∈ rmList, IsT f (v + r))

instance (c₁ c₂ : Fin 8) : Decidable (Concl c₁ c₂) := by unfold Concl; infer_instance

theorem complement_fin : ∀ c₁ c₂ : Fin 8, Hyp c₁ c₂ → Concl c₁ c₂ := by decide +kernel

end CFSG.ClassicalInvolution.Q3.Sec13.AGLFin
