module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

@[expose] def stab2 (a b : Fin 10) : Subgroup (Perm (Fin 10)) where
  carrier := {σ | σ a = a ∧ σ b = b}
  mul_mem' := by
    rintro σ ρ ⟨hσa, hσb⟩ ⟨hρa, hρb⟩
    exact ⟨by simp [Perm.mul_apply, hρa, hσa], by simp [Perm.mul_apply, hρb, hσb]⟩
  one_mem' := ⟨rfl, rfl⟩
  inv_mem' := by
    rintro σ ⟨hσa, hσb⟩
    exact ⟨Perm.inv_eq_iff_eq.2 hσa.symm, Perm.inv_eq_iff_eq.2 hσb.symm⟩

theorem mem_stab2 {a b : Fin 10} {σ : Perm (Fin 10)} : σ ∈ stab2 a b ↔ σ a = a ∧ σ b = b :=
  Iff.rfl

@[expose] def τ₀ : Perm (Fin 10) := swap 8 9

@[expose] def ρ₄ : Perm (Fin 10) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

section Data

variable {G : Type} [Group G]

structure CentData (z : G) (ι : Perm (Fin 10) →* G) : Prop where
  order : orderOf z = 2
  inj : Function.Injective ι
  comm : ∀ σ, z * ι σ = ι σ * z
  ne_z : ∀ σ, ι σ ≠ z
  cases : ∀ g ∈ centralizer ({z} : Set G), ∃ σ, g = ι σ ∨ g = z * ι σ

@[expose] def NoSwapConj (z : G) (ι : Perm (Fin 10) →* G) : Prop :=
  ∀ σ : Perm (Fin 10), σ.IsSwap → ¬ IsConj z (ι σ) ∧ ¬ IsConj z (z * ι σ)

structure SymSec (x : G) (π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)) : Prop where
  surj : Function.Surjective π
  ker : ∀ c : ↥(centralizer ({x} : Set G)), π c = 1 ↔ ((c : G) = 1 ∨ (c : G) = x)

structure OneSided (z : G) (ι : Perm (Fin 10) →* G) (x : G)
    (π : ↥(centralizer ({x} : Set G)) →* Perm (Fin 10)) : Prop where
  eq : x = ι τ₀
  sec : SymSec x π
  swap : ∀ hz : z ∈ centralizer ({x} : Set G), π ⟨z, hz⟩ = τ₀

structure Retraction (z x : G) (κ : ↥(centralizer ({x} : Set G)) →* ℤˣ) : Prop where
  self : κ (selfC x) = -1
  z_one : ∀ hz : z ∈ centralizer ({x} : Set G), κ ⟨z, hz⟩ = 1

variable {z : G} {ι : Perm (Fin 10) →* G}

theorem CentData.mul_self (hC : CentData z ι) : z * z = 1 := by
  rw [← pow_two, ← hC.order]
  exact pow_orderOf_eq_one z

theorem CentData.z_mem_centralizer (hC : CentData z ι) (σ : Perm (Fin 10)) :
    z ∈ centralizer ({ι σ} : Set G) :=
  mem_centralizer_singleton_iff.2 (hC.comm σ)

end Data

end CFSG.OddStandard.AltStdSec.SwapPattern
