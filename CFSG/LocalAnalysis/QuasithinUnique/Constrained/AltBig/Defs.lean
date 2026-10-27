module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup

structure FpfInv (α : Type) [Fintype α] [DecidableEq α] where
  μ : Perm α
  inv : ∀ x, μ (μ x) = x
  fpf : ∀ x, μ x ≠ x

variable {α : Type} [Fintype α] [DecidableEq α]

@[expose] def FpfInv.Contained (p : FpfInv α) (Y : Subgroup (Perm α)) : Prop :=
  ∀ x y, y ≠ x → y ≠ p.μ x → swap x (p.μ x) * swap y (p.μ y) ∈ Y

@[expose] def fixOn (S : Set α) : Subgroup (Perm α) where
  carrier := {σ | ∀ z ∈ S, σ z = z}
  mul_mem' := by
    intro a b ha hb z hz
    simp [Perm.mul_apply, hb z hz, ha z hz]
  one_mem' := by
    intro z _
    rfl
  inv_mem' := by
    intro a ha z hz
    have := ha z hz
    rw [Perm.inv_eq_iff_eq]
    exact this.symm

theorem mem_fixOn {S : Set α} {σ : Perm α} : σ ∈ fixOn S ↔ ∀ z ∈ S, σ z = z := Iff.rfl

end CFSG.QuasithinUnique.L246C127.AltBig
