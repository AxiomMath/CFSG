module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Defs

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup

structure OddInv (α : Type) [Fintype α] [DecidableEq α] where
  μ : Perm α
  ω : α
  inv : ∀ x, μ (μ x) = x
  fix : μ ω = ω
  fpf : ∀ x, x ≠ ω → μ x ≠ x

variable {α : Type} [Fintype α] [DecidableEq α]

@[expose] def OddInv.Contained (p : OddInv α) (Y : Subgroup (Perm α)) : Prop :=
  ∀ x y, x ≠ p.ω → y ≠ p.ω → y ≠ x → y ≠ p.μ x → swap x (p.μ x) * swap y (p.μ y) ∈ Y

theorem OddInv.mu_eq_omega_iff (p : OddInv α) {x : α} : p.μ x = p.ω ↔ x = p.ω := by
  constructor
  · intro h
    have h' := congrArg p.μ h
    rwa [p.inv, p.fix] at h'
  · rintro rfl
    exact p.fix

theorem OddInv.mu_ne_omega (p : OddInv α) {x : α} (hx : x ≠ p.ω) : p.μ x ≠ p.ω :=
  fun h => hx (p.mu_eq_omega_iff.1 h)

end CFSG.QuasithinUnique.L246C127.AltBig
