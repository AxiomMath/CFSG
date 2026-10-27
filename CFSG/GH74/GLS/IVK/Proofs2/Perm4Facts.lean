module

public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

@[expose] def kleinA : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def kleinB : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def kleinFour : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {g | g = 1 ∨ g = kleinA ∨ g = kleinB ∨ g = kleinB * kleinA}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h : ∀ a b : Equiv.Perm (Fin 4),
        (a = 1 ∨ a = kleinA ∨ a = kleinB ∨ a = kleinB * kleinA) →
        (b = 1 ∨ b = kleinA ∨ b = kleinB ∨ b = kleinB * kleinA) →
        a * b = 1 ∨ a * b = kleinA ∨ a * b = kleinB ∨ a * b = kleinB * kleinA := by
      decide +kernel
    exact fun {a b} ha hb => h a b ha hb
  inv_mem' := by
    have h : ∀ a : Equiv.Perm (Fin 4),
        (a = 1 ∨ a = kleinA ∨ a = kleinB ∨ a = kleinB * kleinA) →
        a⁻¹ = 1 ∨ a⁻¹ = kleinA ∨ a⁻¹ = kleinB ∨ a⁻¹ = kleinB * kleinA := by
      decide +kernel
    exact fun {a} ha => h a ha

theorem mem_kleinFour_iff {g : Equiv.Perm (Fin 4)} :
    g ∈ kleinFour ↔ g = 1 ∨ g = kleinA ∨ g = kleinB ∨ g = kleinB * kleinA :=
  Iff.rfl

theorem card_kleinFour : Nat.card ↥kleinFour = 4 := by
  rw [Nat.subtype_card ({1, kleinA, kleinB, kleinB * kleinA} : Finset (Equiv.Perm (Fin 4)))
    (fun g => by simp [mem_kleinFour_iff])]
  decide +kernel

theorem conj_mem_kleinFour (g : Equiv.Perm (Fin 4)) {v : Equiv.Perm (Fin 4)}
    (hv : v ∈ kleinFour) : g * v * g⁻¹ ∈ kleinFour := by
  have h : ∀ g v : Equiv.Perm (Fin 4),
      (v = 1 ∨ v = kleinA ∨ v = kleinB ∨ v = kleinB * kleinA) →
      g * v * g⁻¹ = 1 ∨ g * v * g⁻¹ = kleinA ∨ g * v * g⁻¹ = kleinB ∨
        g * v * g⁻¹ = kleinB * kleinA := by
    decide +kernel
  exact h g v hv

theorem kleinA_mem : kleinA ∈ kleinFour := Or.inr (Or.inl rfl)

theorem kleinB_mem : kleinB ∈ kleinFour := Or.inr (Or.inr (Or.inl rfl))

theorem kleinA_mul_self : kleinA * kleinA = 1 := by decide +kernel

theorem kleinB_mul_self : kleinB * kleinB = 1 := by decide +kernel

theorem kleinA_ne_kleinB : kleinA ≠ kleinB := by decide +kernel

theorem kleinA_ne_one : kleinA ≠ 1 := by decide +kernel

theorem kleinB_ne_one : kleinB ≠ 1 := by decide +kernel

theorem kleinFour_comm : ∀ a ∈ kleinFour, ∀ b ∈ kleinFour, a * b = b * a := by
  have h : ∀ a b : Equiv.Perm (Fin 4),
      (a = 1 ∨ a = kleinA ∨ a = kleinB ∨ a = kleinB * kleinA) →
      (b = 1 ∨ b = kleinA ∨ b = kleinB ∨ b = kleinB * kleinA) → a * b = b * a := by
    decide +kernel
  exact fun a ha b hb => h a b ha hb

theorem card_centralizer_kleinA :
    Nat.card ↥(Subgroup.centralizer ({kleinA} : Set (Equiv.Perm (Fin 4)))) = 8 := by
  rw [Nat.subtype_card (Finset.univ.filter fun g : Equiv.Perm (Fin 4) => g * kleinA = kleinA * g)
    (fun g => by simp [Subgroup.mem_centralizer_singleton_iff])]
  decide +kernel

theorem card_centralizer_kleinB :
    Nat.card ↥(Subgroup.centralizer ({kleinB} : Set (Equiv.Perm (Fin 4)))) = 8 := by
  rw [Nat.subtype_card (Finset.univ.filter fun g : Equiv.Perm (Fin 4) => g * kleinB = kleinB * g)
    (fun g => by simp [Subgroup.mem_centralizer_singleton_iff])]
  decide +kernel

theorem card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

end CFSG.GH74.GLS.IVK.Proofs2
