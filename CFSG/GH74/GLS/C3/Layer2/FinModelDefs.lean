module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup

abbrev Amb (n : ℕ) : Type := Perm (Fin n) × Perm (Fin 4)

@[expose] def x4 : Perm (Fin 4) := swap 0 1 * swap 2 3

@[expose] def Fgrp (n : ℕ) : Subgroup (Amb n) where
  carrier := {p | p.2 * x4 = x4 * p.2 ∧ sign p.1 = sign p.2}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · show b * d * x4 = x4 * (b * d)
      calc b * d * x4 = b * (d * x4) := by rw [mul_assoc]
        _ = b * (x4 * d) := by rw [h3]
        _ = (b * x4) * d := by rw [mul_assoc]
        _ = (x4 * b) * d := by rw [h1]
        _ = x4 * (b * d) := by rw [mul_assoc]
    · show sign (a * c) = sign (b * d)
      rw [map_mul, map_mul, h2, h4]
  inv_mem' := by
    rintro ⟨a, b⟩ ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · show b⁻¹ * x4 = x4 * b⁻¹
      have : x4 * b = b * x4 := h1.symm
      calc b⁻¹ * x4 = b⁻¹ * (x4 * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * x4) * b⁻¹ := by rw [this]
        _ = x4 * b⁻¹ := by group
    · show sign a⁻¹ = sign b⁻¹
      rw [map_inv, map_inv, h2]

@[expose] def sigmaGens (n : ℕ) [NeZero n] : Set (Perm (Fin n)) :=
  {swap 0 1, swap 2 3, swap 0 2 * swap 1 3, swap 4 5}

@[expose] def T0 (n : ℕ) [NeZero n] : Subgroup (Amb n) :=
  Fgrp n ⊓ (Subgroup.closure (sigmaGens n)).prod ⊤

@[expose] def x0 (n : ℕ) : Amb n := (1, x4)

theorem x0_mem_Fgrp (n : ℕ) : x0 n ∈ Fgrp n := by
  refine ⟨rfl, ?_⟩
  show sign (1 : Perm (Fin n)) = sign x4
  simp [x4, Perm.sign_mul]

theorem x0_mem_T0 (n : ℕ) [NeZero n] : x0 n ∈ T0 n :=
  ⟨x0_mem_Fgrp n, one_mem _, trivial⟩

@[expose] def x0T (n : ℕ) [NeZero n] : T0 n := ⟨x0 n, x0_mem_T0 n⟩

@[expose] def Hgrp (n : ℕ) (z : Amb n) : Subgroup (Amb n) := Fgrp n ⊓ Subgroup.centralizer {z}

theorem T0_le_Fgrp (n : ℕ) [NeZero n] : T0 n ≤ Fgrp n := inf_le_left

end CFSG.GH74.GLS.C3.Layer2.Model
