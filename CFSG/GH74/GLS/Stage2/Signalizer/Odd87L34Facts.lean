module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Transport
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Certificate2022
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

open Subgroup CFSG CFSG.ComponentClassification.PSL3Four CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def L34Concl (Y : Type) [Group Y] [Finite Y] (α : MulAut Y) (X : Subgroup (MulAut Y)) : Prop :=
  Nat.card ↥X = 3 ∧ X ⊓ innSub Y = ⊥ ∧ α ∉ innSub Y ⊔ X ∧ IsPGL3Four ↥(innSub Y ⊔ X) ∧
    innSub Y ⊓ centralizer ({α} : Set (MulAut Y)) = innSub Y ⊓ centralizer (X : Set (MulAut Y)) ∧
    IVK.IsL2 ↥(innSub Y ⊓ centralizer ({α} : Set (MulAut Y))) (fun q => q = 4) ∧
    (innSub Y ⊔ X ⊔ zpowers α) ⊓
        centralizer ((innSub Y ⊓ centralizer ({α} : Set (MulAut Y)) : Subgroup (MulAut Y)) :
          Set (MulAut Y)) = X ⊔ zpowers α

theorem l34AutOn_iff (Y : Type) [Group Y] [Finite Y] :
    L34AutOn Y ↔ ∀ (α : MulAut Y) (p : ℕ) (X : Subgroup (MulAut Y)), AutCfg Y α p X → L34Concl Y α X :=
  Iff.rfl

@[expose] def rr : Fin 4 → Equiv.Perm (Fin 42) := ![r₁, r₂, r₃, r₄]

@[expose] def CC : Fin 4 → Subgroup (Equiv.Perm (Fin 42)) := ![C₁, C₂, C₃, C₄]

@[expose] def rrR : Fin 4 → R := ![r₁R, r₂R, r₃R, r₄R]

theorem coe_rrR (i : Fin 4) : ((rrR i : R) : Equiv.Perm (Fin 42)) = rr i := by
  fin_cases i <;> rfl

theorem mem_CC {i : Fin 4} {d : Equiv.Perm (Fin 42)} : d ∈ CC i ↔ rr i * d = d * rr i ∧ d ∈ S := by
  fin_cases i <;>
    simp [CC, rr, C₁, C₂, C₃, C₄, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, eq_comm]

structure L34Facts (z : Equiv.Perm (Fin 42)) : Prop where
  z_mem : z ∈ R
  z_ne : z ≠ 1
  z_cube : z ^ 3 = 1
  z_inv : r₃ * z * r₃⁻¹ = z⁻¹
  z_notS : z ∉ S
  zi_notS : z⁻¹ ∉ S
  rz_notS : r₃ * z ∉ S
  rzi_notS : r₃ * z⁻¹ ∉ S
  z_comm : ∀ d ∈ C₃, d * z = z * d
  cent_le : ∀ s ∈ S, s * z = z * s → s * r₃ = r₃ * s
  scan : ∀ x ∈ R, (∀ d ∈ C₃, d * x = x * d) →
    x = 1 ∨ x = z ∨ x = z⁻¹ ∨ x = r₃ ∨ x = z * r₃ ∨ x = z⁻¹ * r₃
  exp27 : ∀ x ∈ R, x ^ 27 = 1 → x ^ 3 = 1
  wit : ∀ (i : Fin 4) (p : ℕ), (p = 3 ∨ p = 5 ∨ p = 7) → ∀ y ∈ R, y ≠ 1 → y ^ p = 1 →
    rr i * y * rr i * y = 1 →
    (i = 2 ∧ (y = z ∨ y = z⁻¹)) ∨
    (∃ d ∈ CC i, (y * (d * y * d⁻¹)) ^ p ≠ 1) ∨
    (∃ d ∈ CC i, ∃ d' ∈ CC i, (y * (d * y * d⁻¹) * (d' * y * d'⁻¹)) ^ p ≠ 1)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
